-- Prove2me | Theorems.Thm_FulfillFlex_cost_bound
-- name    : FulfillFlex.cost_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:27:44.656563+00:00
-- url     : https://prove2.me/theorems/59e52ab6-c5f4-4255-96c1-1259455b0633
-- title:
--   Appendix B.3.1, p.52 — $C^\pi(\mathbf r,T)\le f(\mathbf r)+O(\sqrt T)$ (corrected: finite demand variance)
-- statement:
--   There is a constant $M$ such that for every $T\ge1$ some spillover limit policy, with limits $\theta$, satisfies
--
--   $$
--   C^\theta(T\mathbf b,T)\le f(T\mathbf b)+M\sqrt T,
--   $$
--
--   where $f(T\mathbf b)$ is the value of the DLP (5) at $m=T\mu$, $r=T\mathbf b$. This is the additive form of Proposition 3, obtained by summing the bounds on local fulfillment, spillover and lost sales.
--
--   Differences from the source:
--   - generalization: O(√T), with O(·) meaning "for sufficiently large T" (§1.2, p.4) → an explicit M, chosen before T, valid for every T ≥ 1; reason: every bound in the proof holds at each T, and the statement for all T ≥ 1 implies the one for large T
--   - generalization: the bound for the policy π of the proof → the existence of some spillover limit vector θ, which may depend on T; reason: the paper's π is such a policy, with θ = f*; the existential is what the goal consumes
--   - correction: demand has a mean μj and nothing more is assumed → E[(D^t_j)²] < ∞ for every j; reason: the proof applies Lemma 7 to D_j(T), and the printed statement is false otherwise. Counterexample satisfying every printed assumption: N = 0, A = {(0,0)}, c = 1, p = 2, P(D ≥ k) = k^(−3/2), b = μ. Then C(Tb,T) ≥ Tμ + E[(D(T) − Tμ)⁺] and f(Tb) = Tμ, and by the generalized CLT E[(D(T) − Tμ)⁺] ≍ T^(2/3), so C/f − 1 ≥ κT^(−1/3)
--   - reading: links A, a set of ordered pairs (p.5) → (j, j) ∈ A for every j; reason: local fulfillment is always available and (5) forces f_jj = 0 off A; Assumption 2 is claimed for Example 1, whose links (1,2), (2,1) force (1,1) ∈ A by transitivity
--   - reading: Proposition 3 and Lemma 8 say "under Assumption 2" → Assumption 1 is also a hypothesis; reason: Assumption 1 is standing from p.6, and the proof uses it (Lemma 8, Case 2; the bound on local fulfillment; linear scaling)
--   - reading: unit demand, inventory r = Tb with b arbitrary → real inventory, one unit per shipment, a DC has inventory when remaining stock ≥ 1; reason: Tb need not be an integer; for integer Tb this is exactly the paper's model
--   - reading: DC j′ "has not fulfilled more than θj′j units" (p.11) → j′ is eligible when spill j′ j + 1 ≤ θ j′ j; reason: the proof says "the policy can not fill more than f∗j′j" (p.51), so at most θ units are filled
--   - reading: "the lowest cost flexible DC" (p.11), ties open → ties go to the smallest index; reason: any fixed rule gives a valid policy, and the proof never uses the order among sources
--   - reading: a unit "not filled locally" abandons independently with probability αj (p.5) → one independent coin per arrival, read exactly when local stock is empty, before a source is sought; reason: the type-one lost sales of the proof (p.51) flip the coin at the stockout; if no source is eligible the order is lost either way
--   - reading: a spillover limit policy may also set an aggregate limit θj (pp.11–12) → no aggregate limit; reason: unspecified limits are non-binding (p.12), and the proof of Proposition 3 sets none
--   - encoding: E[·] of costs and counts → sums in ℝ≥0∞, compared through ENNReal.ofReal; reason: a Bochner integral of a non-integrable function would be 0; path costs are nonnegative under Assumption 1
--   - encoding: daily demand as random variables D^t_j on an unnamed probability space → a PMF ν on DC N → ℕ, with arrivals and coins a PMF on lists; reason: every law on this countable type is a PMF, and no independence across DCs is imposed
-- source:
--   DeValve, Wei, Wu, Yuan, Understanding the Value of Fulfillment Flexibility in an Online Retailing Environment, SSRN 3265838 (2021-01-18 version), Appendix B.3.1, p.52

import Mathlib
import Definitions.Def_FulfillFlex_Assumption1
import Definitions.Def_FulfillFlex_Assumption2
import Definitions.Def_FulfillFlex_IsDLPOptimal
import Definitions.Def_FulfillFlex_meanDemand
import Definitions.Def_FulfillFlex_expectedCost

namespace FulfillFlex

/-- **The cost of `π` is within `O(√T)` of the DLP value.**
DeValve, Wei, Wu, Yuan, SSRN 3265838 (2021-01-18 version), Appendix B.3.1, p.52:
`C^π(r, T) ≤ ∑_j (p_j l*_j + ∑_{j'} c_{jj'} f*_{jj'}) + O(√T) = f(r) + O(√T)`, for `r = T • b`.
The constant `M` is chosen before `T`, and the limits `θ` may depend on `T`. -/
theorem cost_bound {N : ℕ} (A : Set (DC N × DC N)) (c : DC N → DC N → ℝ)
    (p : DC N → ℝ) (α : DC N → unitInterval) (b : DC N → ℝ) (ν : PMF (DC N → ℕ))
    (hdiag : ∀ j, (j, j) ∈ A) (hA1 : Assumption1 A c p) (hA2 : Assumption2 A c)
    (hb : ∀ j, 0 ≤ b j) (hν : FiniteSecondMoment ν) :
    ∃ M : ℝ, ∀ T : ℕ, 1 ≤ T → ∃ θ : DC N → DC N → ℝ,
      expectedCost ν α A c p θ ((T : ℝ) • b) T
        ≤ ENNReal.ofReal
            (dlpValue A c p α ((T : ℝ) • meanDemand ν) ((T : ℝ) • b) + M * √(T : ℝ)) := by sorry

end FulfillFlex
