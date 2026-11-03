-- Prove2me | Theorems.Thm_FulfillFlex_lost_sales_bound
-- name    : FulfillFlex.lost_sales_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:27:34.142983+00:00
-- url     : https://prove2.me/theorems/44d77f1d-7c77-427c-8b8a-5f4ff67f8a7c
-- title:
--   Appendix B.3.1, pp.51–52 — under $\pi$, expected lost sales are at most $l^*_j+O(\sqrt T)$ (corrected: finite demand variance)
-- statement:
--   There is a constant $M$ such that for every $T\ge1$, every structured optimal solution $(f^*,l^*)$ of the DLP (5) at $m=T\mu$, $r=T\mathbf b$, and every DC $j$, the spillover limit policy with limits $\theta=f^*$ satisfies
--
--   $$
--   \mathbb E[\text{lost sales at }j]\le l^*_j+M\sqrt T.
--   $$
--
--   This is the third and hardest part of the proof of Proposition 3. Together with the bounds on fulfillment it gives the cost bound.
--
--   **Formalization Note** $M$ is chosen before $T$ and the solution, and it does not depend on them or on $j$.
--
--   Differences from the source:
--   - generalization: O(√T), with O(·) meaning "for sufficiently large T" (§1.2, p.4) → an explicit M, chosen before T and before the structured optimal solution (f*, l*) and the DC j, valid for every T ≥ 1; reason: every bound in the proof holds at each T, its constants (½√(α_j(1−α_j)μ_j), ½σ_j, ½σ_j′, O(1) rounding) do not depend on (f*, l*), and the statement for all T ≥ 1 and every such solution implies the one for large T and the chosen solution
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
--   DeValve, Wei, Wu, Yuan, Understanding the Value of Fulfillment Flexibility in an Online Retailing Environment, SSRN 3265838 (2021-01-18 version), Appendix B.3.1, "Lost Sales", pp.51–52

import Mathlib
import Definitions.Def_FulfillFlex_Assumption1
import Definitions.Def_FulfillFlex_IsDLPOptimal
import Definitions.Def_FulfillFlex_meanDemand
import Definitions.Def_FulfillFlex_expectedCost

namespace FulfillFlex

/-- **Lost sales under `π`.**
DeValve, Wei, Wu, Yuan, SSRN 3265838 (2021-01-18 version), Appendix B.3.1, "Lost Sales", pp.51–52:
"under π, the expected amount of lost sales at DC j is bound by l∗j + O(√T)". The constant `M` is
chosen before the horizon `T` and the optimal solution `(f*, l*)`, and it is uniform in them and
in the DC `j`.

**Formalization Note** `π` is the spillover limit policy with limits `θ = f*`. The hypotheses are
the paper's standing ones and finite second moments of daily demand. -/
theorem lost_sales_bound {N : ℕ} (A : Set (DC N × DC N)) (c : DC N → DC N → ℝ)
    (p : DC N → ℝ) (α : DC N → unitInterval) (b : DC N → ℝ) (ν : PMF (DC N → ℕ))
    (hdiag : ∀ j, (j, j) ∈ A) (hA1 : Assumption1 A c p) (hb : ∀ j, 0 ≤ b j)
    (hν : FiniteSecondMoment ν) :
    ∃ M : ℝ, ∀ T : ℕ, 1 ≤ T → ∀ (f : DC N → DC N → ℝ) (l : DC N → ℝ),
      IsStructuredOptimal A c p α ((T : ℝ) • meanDemand ν) ((T : ℝ) • b) f l →
        ∀ j, expectedLost ν α A c f ((T : ℝ) • b) T j ≤ ENNReal.ofReal (l j + M * √(T : ℝ)) := by sorry

end FulfillFlex
