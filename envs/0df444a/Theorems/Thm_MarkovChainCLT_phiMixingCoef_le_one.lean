-- Prove2me | Theorems.Thm_MarkovChainCLT_phiMixingCoef_le_one
-- name    : MarkovChainCLT.phiMixingCoef_le_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-04T23:17:18.216809+00:00
-- url     : https://prove2.me/theorems/247a3098-d367-483a-b9bc-9713a0007275
-- title:
--   $\varphi(n)\le 1$
-- statement:
--   The uniform mixing coefficient is at most one.
--
--   Let $Y_0,Y_1,\dots$ be random variables on a probability space $(\Omega,\mathcal F,P)$ and $n\ge 0$. With $\varphi(n)$ as above,
--
--   $$
--   \varphi(n)\le 1.
--   $$
--
--   Each element $|P(B\mid A)-P(B)|$ has both terms in $[0,1]$, so their difference lies in $[-1,1]$.
--
--   **Formalization Note** Lean encodes $\varphi(n)$ as a real supremum.
-- source:
--   Galin L. Jones, On the Markov chain central limit theorem, Probability Surveys 1 (2004) 299-320, Sec 3 Definition 3

import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ProbabilityTheory ENNReal

theorem MarkovChainCLT.phiMixingCoef_le_one {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E) (n : ℕ) : phiMixingCoef P Y n ≤ 1 := by sorry
