-- Prove2me | Theorems.Thm_HealthRefPricing_PriceCompare_vp_below_rp_at_one
-- name    : HealthRefPricing.PriceCompare.vp_below_rp_at_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:23:44.462971+00:00
-- url     : https://prove2.me/theorems/76b7d38e-a944-46bc-ab07-b27ec91f9f1f
-- title:
--   Proof of Proposition 5, Appendix pp. 9–10 (PDF 42–43) — at λ = 1 every VP equilibrium price is below its RP counterpart
-- statement:
--   Consider the two-provider model under the standing assumptions, with Assumption 1 at cost share $\lambda = 1$, Assumption 2, and $\tilde c < p^*$. Let $P^{RP}$ be a Nash equilibrium of the reference-pricing game and $P^{VP}$ a Nash equilibrium of the variable-payment game at cost share $\lambda = 1$. Then for each provider $j$,
--
--   $$p^{VP}_j < p^{RP}_j .$$
--
--   When patients pay the full price, every provider charges less under variable payment than under reference pricing. Together with the monotonicity of VP prices in $\lambda$ (Lemma 2(a)) and their blow-up as $\lambda \to 0$, this gives the threshold of Proposition 5.
--
--   **Formalization Note** Provider $j$ ranges over `Fin 2`, index `0` being the paper's provider 1. The paper's phrase "as $\lambda$ approaches 1, each of the provider prices under VP approaches a value lower than its RP counterparts" is read as the strict comparison at $\lambda = 1$, which is what its Cases 1–3 prove. The hypothesis $\tilde c < p^*$ is used in Case 2 of the proof ("knowing that $\tilde c < p^*$"); without it the comparison fails in numerical instances.
-- source:
--   Nassiri, Adida & Mamani, Reference pricing for healthcare services, author manuscript (SSRN 3176280, version of Dec. 28, 2020; eScholarship 3sm502rz), Appendix pp. 9–10 (PDF 42–43), proof of Proposition 5, Cases 1–3

import Mathlib
import Definitions.Def_HealthRefPricing_PriceCompare_Model

namespace HealthRefPricing.PriceCompare

/-- Proof of Proposition 5, Cases 1–3 (Appendix pp. 9–10): at cost share `1` each provider's
variable-payment equilibrium price is strictly below its reference-pricing equilibrium price. -/
theorem vp_below_rp_at_one (P : Params) (hS : P.Standing) (hA1 : Assumption1 P 1)
    (hA2 : Assumption2 P) (hct : P.ct < P.ps) (pRP : Fin 2 → ℝ) (hRP : IsEqRP P pRP)
    (p : Fin 2 → ℝ) (hp : IsEqVP P 1 p) (j : Fin 2) :
    p j < pRP j := by sorry

end HealthRefPricing.PriceCompare
