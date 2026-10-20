-- Prove2me | Theorems.Thm_HealthRefPricing_PriceCompare_lemma_2a
-- name    : HealthRefPricing.PriceCompare.lemma_2a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:23:34.44842+00:00
-- url     : https://prove2.me/theorems/5a32261a-f81e-4732-8b5b-c85a84c8e1ce
-- title:
--   Lemma 2(a), p. 17 (PDF 18) — under variable payment each provider's equilibrium price is decreasing in the cost share λ
-- statement:
--   Consider the two-provider model under the standing assumptions. Let $0 < \lambda < \lambda' \le 1$ be two cost shares at which Assumption 1 holds, and let $P = (p_1, p_2)$ and $P' = (p'_1, p'_2)$ be Nash equilibria of the variable-payment price game at cost shares $\lambda$ and $\lambda'$ respectively. Then for each provider $j$,
--
--   $$p'_j < p_j .$$
--
--   That is, each provider's equilibrium price under variable payment is strictly decreasing in the cost share. As patients bear a larger fraction of the price, providers lower their prices; this monotonicity is one of the two ingredients of the threshold structure in Proposition 5.
--
--   **Formalization Note** Provider $j$ ranges over `Fin 2`, index `0` being the paper's provider 1. "Decreasing" is read as strictly decreasing; the paper writes "non-increasing" when it means the weak form (Lemma 3(b), same page). Only part (a) of Lemma 2 is formalized.
-- source:
--   Nassiri, Adida & Mamani, Reference pricing for healthcare services, author manuscript (SSRN 3176280, version of Dec. 28, 2020; eScholarship 3sm502rz), p. 17 (PDF 18), Lemma 2(a); proof Appendix p. 8 (PDF 41)

import Mathlib
import Definitions.Def_HealthRefPricing_PriceCompare_Model

namespace HealthRefPricing.PriceCompare

/-- Lemma 2(a) (p. 17): under variable payment each provider's equilibrium price is strictly
decreasing in the cost share. -/
theorem lemma_2a (P : Params) (hS : P.Standing) (lam lam' : ℝ) (hlam : 0 < lam)
    (hlt : lam < lam') (hle : lam' ≤ 1) (hA1 : Assumption1 P lam) (hA1' : Assumption1 P lam')
    (p p' : Fin 2 → ℝ) (hp : IsEqVP P lam p) (hp' : IsEqVP P lam' p') (j : Fin 2) :
    p' j < p j := by sorry

end HealthRefPricing.PriceCompare
