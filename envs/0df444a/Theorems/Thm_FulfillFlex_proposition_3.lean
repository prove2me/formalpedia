-- Prove2me | Theorems.Thm_FulfillFlex_proposition_3
-- name    : FulfillFlex.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:27:29.764666+00:00
-- url     : https://prove2.me/theorems/927a3d04-7f6d-4252-be73-4696d9387b51
-- title:
--   Proposition 3, p.16 — a spillover limit policy costs at most $(1+O(T^{-1/2}))$ times the DLP value (corrected: finite demand variance)
-- statement:
--   Consider the fulfillment model with $N+1$ DCs, links $A$ containing the diagonal, costs $c,p$ satisfying Assumptions 1 and 2, abandonment probabilities $\alpha\in[0,1]^{N+1}$, base inventories $\mathbf b\ge0$, and i.i.d. daily demand with an arbitrary joint law across DCs and finite second moments. Then there is a constant $M$ such that for every horizon $T\ge1$ some spillover limit policy, with limits $\theta$, satisfies
--
--   $$
--   C^\theta(T\mathbf b,T)\le\Bigl(1+\frac{M}{\sqrt T}\Bigr)f(T\mathbf b),
--   $$
--
--   where $f(T\mathbf b)$ is the value of the deterministic LP (5) at horizon $T$.
--
--   This is the paper's asymptotic optimality result: together with the lower bound $f\le C^*$ of the paper (not part of this mission), it shows that spillover limit policies are asymptotically optimal under a general network structure with customer abandonment, while satisfying the local no-holdback requirement.
--
--   **Formalization Note** $M$ does not depend on $T$; the limits $\theta$ may.
--
--   Differences from the source:
--   - correction: demand has a mean μj and nothing more is assumed → E[(D^t_j)²] < ∞ for every j; reason: the proof applies Lemma 7 to D_j(T), and the printed statement is false otherwise. Counterexample satisfying every printed assumption: N = 0, A = {(0,0)}, c = 1, p = 2, P(D ≥ k) = k^(−3/2), b = μ. Then C(Tb,T) ≥ Tμ + E[(D(T) − Tμ)⁺] and f(Tb) = Tμ, and by the generalized CLT E[(D(T) − Tμ)⁺] ≍ T^(2/3), so C/f − 1 ≥ κT^(−1/3)
--   - encoding: the ratio Cπ(r,T)/f(r) ≤ 1 + O(T^(−1/2)) → the product form C^θ ≤ (1 + M/√T)·f; reason: equivalent when f > 0; f = 0 forces all μ_j = 0, hence zero demand and zero cost; Lean's x / 0 = 0 would change the claim
--   - generalization: O(T^(−1/2)), with O(·) meaning "for sufficiently large T" (§1.2, p.4) → an explicit M, chosen before T, valid for every T ≥ 1; reason: every bound in the proof holds at each T, and the statement for all T ≥ 1 implies the one for large T
--   - generalization: "there exists a policy π" → there exist spillover limits θ (depending on T); reason: a spillover limit policy is a policy, and the paper's π is one (p.17, p.50); this avoids defining all LNH policies
--   - reading: links A, a set of ordered pairs (p.5) → (j, j) ∈ A for every j; reason: local fulfillment is always available and (5) forces f_jj = 0 off A; Assumption 2 is claimed for Example 1, whose links (1,2), (2,1) force (1,1) ∈ A by transitivity
--   - reading: Proposition 3 and Lemma 8 say "under Assumption 2" → Assumption 1 is also a hypothesis; reason: Assumption 1 is standing from p.6, and the proof uses it (Lemma 8, Case 2; the bound on local fulfillment; linear scaling)
--   - reading: unit demand, inventory r = Tb with b arbitrary → real inventory, one unit per shipment, a DC has inventory when remaining stock ≥ 1; reason: Tb need not be an integer; for integer Tb this is exactly the paper's model
--   - reading: DC j′ "has not fulfilled more than θj′j units" (p.11) → j′ is eligible when spill j′ j + 1 ≤ θ j′ j; reason: the proof says "the policy can not fill more than f∗j′j" (p.51), so at most θ units are filled
--   - reading: "the lowest cost flexible DC" (p.11), ties open → ties go to the smallest index; reason: any fixed rule gives a valid policy, and the proof never uses the order among sources
--   - reading: a unit "not filled locally" abandons independently with probability αj (p.5) → one independent coin per arrival, read exactly when local stock is empty, before a source is sought; reason: the type-one lost sales of the proof (p.51) flip the coin at the stockout; if no source is eligible the order is lost either way
--   - reading: a spillover limit policy may also set an aggregate limit θj (pp.11–12) → no aggregate limit; reason: unspecified limits are non-binding (p.12), and the proof of Proposition 3 sets none
--   - encoding: E[·] of costs and counts → sums in ℝ≥0∞, compared through ENNReal.ofReal; reason: a Bochner integral of a non-integrable function would be 0; path costs are nonnegative under Assumption 1
--   - encoding: daily demand as random variables D^t_j on an unnamed probability space → a PMF ν on DC N → ℕ, with arrivals and coins a PMF on lists; reason: every law on this countable type is a PMF, and no independence across DCs is imposed
--   - encoding: DCs 0 ≤ j ≤ N → Fin (N + 1); `c j j′` is c_{jj′}; reason: same index set, source first
-- source:
--   DeValve, Wei, Wu, Yuan, Understanding the Value of Fulfillment Flexibility in an Online Retailing Environment, SSRN 3265838 (2021-01-18 version), Proposition 3, p.16 (restated p.50; proof pp.50–52)

import Mathlib
import Definitions.Def_FulfillFlex_Assumption1
import Definitions.Def_FulfillFlex_Assumption2
import Definitions.Def_FulfillFlex_dlpValue
import Definitions.Def_FulfillFlex_meanDemand
import Definitions.Def_FulfillFlex_expectedCost

namespace FulfillFlex

/-- **Proposition 3 (a spillover limit policy is asymptotically optimal).**
DeValve, Wei, Wu, Yuan, SSRN 3265838 (2021-01-18 version), Proposition 3, p.16: "Under Assumption 2,
for each T > 0 and r = Tb, there exists a policy π, with cost denoted by Cπ(r,T), that satisfies
Cπ(r,T)/f(r) ≤ 1 + O(T^(-1/2))."

There is a constant `M`, chosen before `T`, such that for every horizon `T ≥ 1` some spillover
limit policy with limits `θ` has `C^θ(T • b, T) ≤ (1 + M / √T) · f(T • b)`.

**Formalization Note** The ratio is written multiplicatively, since Lean's `x / 0 = 0` would change
the claim at `f = 0`. Demand has finite second moments (a correction: the printed statement is
false without it). Assumption 1 is standing from p.6, and the links contain the diagonal. The law
`ν` of the daily demand vector is arbitrary, with no independence across DCs. -/
theorem proposition_3 {N : ℕ} (A : Set (DC N × DC N)) (c : DC N → DC N → ℝ)
    (p : DC N → ℝ) (α : DC N → unitInterval) (b : DC N → ℝ) (ν : PMF (DC N → ℕ))
    (hdiag : ∀ j, (j, j) ∈ A) (hA1 : Assumption1 A c p) (hA2 : Assumption2 A c)
    (hb : ∀ j, 0 ≤ b j) (hν : FiniteSecondMoment ν) :
    ∃ M : ℝ, ∀ T : ℕ, 1 ≤ T → ∃ θ : DC N → DC N → ℝ,
      expectedCost ν α A c p θ ((T : ℝ) • b) T
        ≤ ENNReal.ofReal
            ((1 + M / √(T : ℝ)) * dlpValue A c p α ((T : ℝ) • meanDemand ν) ((T : ℝ) • b)) := by sorry

end FulfillFlex
