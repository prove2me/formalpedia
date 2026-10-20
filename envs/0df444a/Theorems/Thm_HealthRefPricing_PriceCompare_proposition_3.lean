-- Prove2me | Theorems.Thm_HealthRefPricing_PriceCompare_proposition_3
-- name    : HealthRefPricing.PriceCompare.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:23:43.505055+00:00
-- url     : https://prove2.me/theorems/ef53ec40-c2b1-4b92-92bf-107fee92608e
-- title:
--   Proposition 3, p. 14 (PDF 15) — if provider 1 is non-value-based at the RP equilibrium, so is provider 2
-- statement:
--   Consider the two-provider model under reference pricing, under the standing assumptions (in particular $a_1 \le a_2$) and Assumption 2, and let $P = (p_1, p_2)$ be a Nash equilibrium of the reference-pricing price game. If provider 1 is non-value-based, $p_1 > p^*$, then provider 2 is non-value-based:
--
--   $$p_1 > p^* \implies p_2 > p^* .$$
--
--   The provider with the better non-price attribute is the one more willing to charge above the reference price; with Theorem 2 this leaves at most two candidate status patterns to test.
--
--   **Formalization Note** Providers are indexed by `Fin 2`: index `0` is the paper's provider 1 and index `1` is provider 2, so the statement reads `¬ IsValueBased P p 0 → ¬ IsValueBased P p 1`.
-- source:
--   Nassiri, Adida & Mamani, Reference pricing for healthcare services, author manuscript (SSRN 3176280, version of Dec. 28, 2020; eScholarship 3sm502rz), p. 14 (PDF 15), Proposition 3; proof Appendix pp. 6–7 (PDF 39–40)

import Mathlib
import Definitions.Def_HealthRefPricing_PriceCompare_Model

namespace HealthRefPricing.PriceCompare

/-- Proposition 3 (p. 14): at a reference-pricing equilibrium, if provider 1 (index `0`) is
non-value-based then so is provider 2 (index `1`). -/
theorem proposition_3 (P : Params) (hS : P.Standing) (hA2 : Assumption2 P)
    (p : Fin 2 → ℝ) (hp : IsEqRP P p) (h0 : ¬ IsValueBased P p 0) :
    ¬ IsValueBased P p 1 := by sorry

end HealthRefPricing.PriceCompare
