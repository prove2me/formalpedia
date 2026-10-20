-- Prove2me | Theorems.Thm_HealthRefPricing_PriceCompare_proposition_2
-- name    : HealthRefPricing.PriceCompare.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:23:38.141761+00:00
-- url     : https://prove2.me/theorems/1132bf3f-ae7a-4bef-919d-d0bc2f444944
-- title:
--   Proposition 2, p. 13 (PDF 14) — at an RP equilibrium a value-based provider prices at the reference price p∗
-- statement:
--   Consider the two-provider model under reference pricing, under the standing assumptions and Assumption 2. Let $P = (p_1,p_2)$ be a Nash equilibrium of the reference-pricing price game, and let provider $j$ be value-based at $P$, i.e. $p_j \le p^*$. Then
--
--   $$p_j = p^* .$$
--
--   A patient who chooses a value-based provider pays only the co-payment $\tilde c$, so the provider's price below $p^*$ does not affect its market share but does raise its revenue; value-based providers therefore price exactly at the cap ("shadow pricing").
--
--   **Formalization Note** Provider $j$ ranges over `Fin 2`, index `0` being the paper's provider 1. Value-based means $p_j \le p^*$ (see the Model definition).
-- source:
--   Nassiri, Adida & Mamani, Reference pricing for healthcare services, author manuscript (SSRN 3176280, version of Dec. 28, 2020; eScholarship 3sm502rz), p. 13 (PDF 14), Proposition 2; proof Appendix p. 5 (PDF 38)

import Mathlib
import Definitions.Def_HealthRefPricing_PriceCompare_Model

namespace HealthRefPricing.PriceCompare

/-- Proposition 2 (p. 13): at a reference-pricing equilibrium a value-based provider prices
exactly at the reference price. -/
theorem proposition_2 (P : Params) (hS : P.Standing) (hA2 : Assumption2 P)
    (p : Fin 2 → ℝ) (hp : IsEqRP P p) (j : Fin 2) (hj : IsValueBased P p j) :
    p j = P.ps := by sorry

end HealthRefPricing.PriceCompare
