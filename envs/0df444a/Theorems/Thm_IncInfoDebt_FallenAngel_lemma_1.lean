-- Prove2me | Theorems.Thm_IncInfoDebt_FallenAngel_lemma_1
-- name    : IncInfoDebt.FallenAngel.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:18:15.10842+00:00
-- url     : https://prove2.me/theorems/78aa1cc1-752a-4b13-944a-430468390bbe
-- title:
--   Lemma 1 — normalization and positive survival of the killed density
-- statement:
--   Consider the drifted log distance with volatility $\sigma>0$, lag $L>0$, arbitrary drift $m$, and observed lagged state $a>0$. Let $K_L(a,y)$ be the killed Gaussian transition density in (D.2), and let $S_L(a)$ be the survival expression in (D.3). Then
--
--   $$\int_0^\infty K_L(a,y)\,dy=S_L(a)>0.$$
--
--   The first identity is the normalization step of Lemma 1: it makes $K_L(a,y)/S_L(a)$ the conditional density in (D.1). Positivity makes its denominator well defined.
--
--   **Formalization Note** Strict positivity is made explicit for $a>0$; the paper uses it implicitly when dividing by the conditional survival probability.
-- source:
--   Benzoni, Garlappi & Goldstein, Federal Reserve Bank of Chicago WP 2019-08 (20 Sept 2019), Online Appendix pp. 11–12, Lemma 1, (D.1)–(D.3), https://doi.org/10.21033/wp-2019-08

import Mathlib
import Definitions.Def_IncInfoDebt_FallenAngel_Model

namespace IncInfoDebt.FallenAngel
open MeasureTheory

/-- Lemma 1, Online Appendix pp. 11–12: integrating (D.2) gives (D.3). -/
theorem lemma_1 (σ m L a : ℝ) (hP : Standing σ L) (ha : 0 < a) :
    (∫ y in Set.Ioi (0 : ℝ), killedDensity σ m L a y) = survival σ m L a ∧
    0 < survival σ m L a := by sorry

end IncInfoDebt.FallenAngel
