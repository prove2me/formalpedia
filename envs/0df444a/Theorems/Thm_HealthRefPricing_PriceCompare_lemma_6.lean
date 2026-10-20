-- Prove2me | Theorems.Thm_HealthRefPricing_PriceCompare_lemma_6
-- name    : HealthRefPricing.PriceCompare.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:23:36.062319+00:00
-- url     : https://prove2.me/theorems/65f2333a-7000-4ce4-938f-4b3cc1fc2465
-- title:
--   Lemma 6, Appendix p. 6 (PDF 39) — provider j is value-based iff 1 − γ(p∗ − c)(1 − S^RP_j(p_j = p∗, P_−j)) ≤ 0
-- statement:
--   Consider the two-provider model under reference pricing, under the standing assumptions and Assumption 2, and let $P = (p_1, p_2)$ be a Nash equilibrium of the reference-pricing price game. Write $S^{RP}_j(p_j = p^*, P_{-j})$ for provider $j$'s market share when $j$ charges $p^*$ and the other provider keeps its equilibrium price. Then provider $j$ is value-based ($p_j \le p^*$) if and only if
--
--   $$1 - \gamma(p^* - c)\bigl(1 - S^{RP}_j(p_j = p^*, P_{-j})\bigr) \le 0 .$$
--
--   The left-hand side is, up to a positive factor, the right derivative of provider $j$'s profit at $p^*$; the lemma is the test used to decide each provider's status in the proofs of Proposition 3 and Proposition 5.
--
--   **Formalization Note** Provider $j$ ranges over `Fin 2`, index `0` being the paper's provider 1. The profile $(p_j = p^*, P_{-j})$ is `Function.update p j ps`.
-- source:
--   Nassiri, Adida & Mamani, Reference pricing for healthcare services, author manuscript (SSRN 3176280, version of Dec. 28, 2020; eScholarship 3sm502rz), Appendix pp. 6–7 (PDF 39–40), Lemma 6 (in the proof of Proposition 3)

import Mathlib
import Definitions.Def_HealthRefPricing_PriceCompare_Model

namespace HealthRefPricing.PriceCompare

/-- Lemma 6 (Appendix p. 6): at a reference-pricing equilibrium provider `j` is value-based iff
`1 - γ(p* - c)(1 - S^{RP}_j(p_j = p*, P_{-j})) ≤ 0`. -/
theorem lemma_6 (P : Params) (hS : P.Standing) (hA2 : Assumption2 P)
    (p : Fin 2 → ℝ) (hp : IsEqRP P p) (j : Fin 2) :
    IsValueBased P p j ↔
      1 - P.γ * (P.ps - P.c) * (1 - share P (oopRP P (Function.update p j P.ps)) j) ≤ 0 := by sorry

end HealthRefPricing.PriceCompare
