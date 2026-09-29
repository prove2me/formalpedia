-- Prove2me | Theorems.Thm_MarkovChainCLT_alphaMixingCoef_le_one
-- name    : MarkovChainCLT.alphaMixingCoef_le_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-04T23:36:57.449323+00:00
-- url     : https://prove2.me/theorems/d0400bc5-ff67-4543-aae1-56319006275a
-- title:
--   $\alpha(n)\le 1$
-- statement:
--   The strong mixing coefficient is at most one.
--
--   With $\alpha(n)$ as above,
--
--   $$
--   \alpha(n)\le 1.
--   $$
--
--   Each $|P(A\cap B)-P(A)P(B)|$ has both terms in $[0,1]$.
--
--   **Formalization Note** Real supremum.
-- source:
--   Jones 2004 Sec 3 Definition 1

import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ProbabilityTheory ENNReal

theorem MarkovChainCLT.alphaMixingCoef_le_one {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E) (n : ℕ) : alphaMixingCoef P Y n ≤ 1 := by sorry
