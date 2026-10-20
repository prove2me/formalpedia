-- Prove2me | Theorems.Thm_HealthRefPricing_PriceCompare_case_1
-- name    : HealthRefPricing.PriceCompare.case_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:23:46.497984+00:00
-- url     : https://prove2.me/theorems/eb65b862-6769-4a87-bb2d-9efe43514e4f
-- title:
--   Proof of Proposition 5, Case 1, Appendix p. 9 (PDF 42) — both providers value-based under RP ⇒ p^VP_1 ≤ p^VP_2 < p∗ at λ = 1
-- statement:
--   Consider the two-provider model under the standing assumptions, with Assumption 1 at cost share $\lambda = 1$ and Assumption 2. Let $P^{RP} = (p^{RP}_1, p^{RP}_2)$ be a Nash equilibrium of the reference-pricing game at which both providers are value-based ($p^{RP}_1 \le p^*$ and $p^{RP}_2 \le p^*$), and let $P^{VP} = (p^{VP}_1, p^{VP}_2)$ be a Nash equilibrium of the variable-payment game at cost share $\lambda = 1$. Then
--
--   $$p^{VP}_1 \le p^{VP}_2 < p^* .$$
--
--   Since both RP prices equal $p^*$ (Proposition 2), this is the first of the three cases showing that at full cost share every VP price lies below its RP counterpart.
--
--   **Formalization Note** Providers are indexed by `Fin 2`: index `0` is the paper's provider 1 and index `1` is provider 2. The paper's "assuming without loss of generality that $p^{VP}_2 \ge p^{VP}_1$" is a consequence of $a_1 \le a_2$ and is stated here as part of the conclusion, not as a hypothesis. The paper's "assuming $\tilde c \le c$" is covered by the standing assumption $\tilde c < c$.
-- source:
--   Nassiri, Adida & Mamani, Reference pricing for healthcare services, author manuscript (SSRN 3176280, version of Dec. 28, 2020; eScholarship 3sm502rz), Appendix p. 9 (PDF 42), proof of Proposition 5, Case 1

import Mathlib
import Definitions.Def_HealthRefPricing_PriceCompare_Model

namespace HealthRefPricing.PriceCompare

/-- Case 1 of the proof of Proposition 5 (Appendix p. 9): if both providers are value-based at
the RP equilibrium, then at the VP equilibrium with cost share `1` we have `p^{VP}_1 ≤ p^{VP}_2 < p*`. -/
theorem case_1 (P : Params) (hS : P.Standing) (hA1 : Assumption1 P 1) (hA2 : Assumption2 P)
    (pRP : Fin 2 → ℝ) (hRP : IsEqRP P pRP) (h0 : IsValueBased P pRP 0) (h1 : IsValueBased P pRP 1)
    (p : Fin 2 → ℝ) (hp : IsEqVP P 1 p) :
    p 0 ≤ p 1 ∧ p 1 < P.ps := by sorry

end HealthRefPricing.PriceCompare
