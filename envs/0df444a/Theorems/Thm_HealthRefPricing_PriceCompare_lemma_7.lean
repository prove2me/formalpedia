-- Prove2me | Theorems.Thm_HealthRefPricing_PriceCompare_lemma_7
-- name    : HealthRefPricing.PriceCompare.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:23:39.957428+00:00
-- url     : https://prove2.me/theorems/167ec8c5-2446-4f6b-89ba-7210ab6fd9dd
-- title:
--   Lemma 7 (final claim), Appendix p. 9 (PDF 42) — for p2 > c + 1/γ, provider 1's RP best response exceeds its VP best response
-- statement:
--   Consider the two-provider model under the standing assumptions, with Assumption 1 at cost share $\lambda = 1$, Assumption 2, and $\tilde c < p^*$. Fix a price $p_2 > c + 1/\gamma$ of provider 2. Let $p^{RP}_1(p_2)$ be a best response of provider 1 to $p_2$ under reference pricing and $p^{VP}_1(p_2)$ a best response of provider 1 to $p_2$ under variable payment with cost share $1$. Then
--
--   $$p^{RP}_1(p_2) > p^{VP}_1(p_2) .$$
--
--   This is the comparison of best-response curves that drives Case 2 of the proof of Proposition 5 (both providers non-value-based), where it yields $p^{VP}_2 < p^{RP}_2$.
--
--   **Formalization Note** Providers are indexed by `Fin 2`: index `0` is the paper's provider 1 and index `1` is provider 2, so the best responses are those of index `0` to the rival price $p_2$. Only the final claim of Lemma 7 is formalized, in the form its proof concludes ("$g(p_2) - f(p_2) \ge 0$. That is, that $p^{RP}_1(p_2) > p^{VP}_1(p_2)$"), and with cost share $\lambda = 1$, which is the cost share at which the paper's $f$ is written; the monotonicity of $f$ and $g$ at their roots is not formalized. The hypothesis $\tilde c < p^*$ is the one the surrounding proof uses ("knowing that $\tilde c < p^*$").
-- source:
--   Nassiri, Adida & Mamani, Reference pricing for healthcare services, author manuscript (SSRN 3176280, version of Dec. 28, 2020; eScholarship 3sm502rz), Appendix p. 9 (PDF 42), Lemma 7 and its proof ('With some algebra we can show that g(p2) − f(p2) ≥ 0. That is, that p^RP_1(p2) > p^VP_1(p2).')

import Mathlib
import Definitions.Def_HealthRefPricing_PriceCompare_Model

namespace HealthRefPricing.PriceCompare

/-- Lemma 7, final claim (Appendix p. 9, as concluded in its proof): for every price
`p₂ > c + 1/γ` of provider 2, provider 1's best response under reference pricing is strictly above
its best response under variable payment with cost share `1`. -/
theorem lemma_7 (P : Params) (hS : P.Standing) (hA1 : Assumption1 P 1) (hA2 : Assumption2 P)
    (hct : P.ct < P.ps) (p2 : ℝ) (hp2 : P.c + 1 / P.γ < p2) (xRP xVP : ℝ)
    (hRP : IsBestRespRP P 0 p2 xRP) (hVP : IsBestRespVP P 1 0 p2 xVP) :
    xVP < xRP := by sorry

end HealthRefPricing.PriceCompare
