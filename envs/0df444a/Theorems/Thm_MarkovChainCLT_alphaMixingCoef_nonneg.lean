-- Prove2me | Theorems.Thm_MarkovChainCLT_alphaMixingCoef_nonneg
-- name    : MarkovChainCLT.alphaMixingCoef_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-04T23:36:54.499255+00:00
-- url     : https://prove2.me/theorems/2d0e0570-4140-4127-b8b7-c88dc72baf1b
-- title:
--   $\alpha(n)\ge 0$
-- statement:
--   The strong mixing coefficient is nonnegative.
--
--   With $\alpha(n)$ the supremum over $k$, $A\in\sigma(Y_0,\dots,Y_k)$, $B\in\sigma(Y_{k+n},\dots)$ of $|P(A\cap B)-P(A)P(B)|$,
--
--   $$
--   0\le\alpha(n).
--   $$
--
--   Indeed $0$ is attained at $A=B=\Omega$.
--
--   **Formalization Note** Real supremum over the indicated sets.
-- source:
--   Jones 2004 Sec 3 Definition 1

import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ProbabilityTheory ENNReal

theorem MarkovChainCLT.alphaMixingCoef_nonneg {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E) (n : ℕ) : 0 ≤ alphaMixingCoef P Y n := by sorry
