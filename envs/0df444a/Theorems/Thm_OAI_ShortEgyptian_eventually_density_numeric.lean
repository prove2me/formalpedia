-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_eventually_density_numeric
-- name    : OAI.ShortEgyptian.eventually_density_numeric
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:47:36.986152+00:00
-- url     : https://prove2.me/theorems/e9b4325f-57ce-40f9-927c-2290a8549d59
-- title:
--   The unrolled density bound is eventually at most $1/8$
-- statement:
--   Fix the constants $d_M=2002\cdot102=204204$, $d_X=d_M+2$ and $R=49009440000$. For a real number $S$ let $m(S)=\lfloor S/\log S\rfloor$ and $\operatorname{depth}(S)=\big\lceil (d_XS-m(S))/(m(S)/10000)\big\rceil$ (natural-number floor and ceiling). Then there is $S_0\in\mathbb R$ such that for every real $S\ge S_0$
--
--   $$
--   \operatorname{depth}(S)\,\exp\Big(2R\,S^{1/4}-\frac{m(S)}{1000}\,S^{-1/4}\Big)\le\frac18 .
--   $$
--
--   The left-hand side is the bound for the density of bad numerators at the top level, obtained by unrolling the level-by-level density recurrence through all $\operatorname{depth}(S)$ levels. Since $m(S)\approx S/\log S$ is much larger than $S^{1/2}$ while $\operatorname{depth}(S)=O(\log S)$, the exponent is eventually very negative. The statement turns this into the explicit threshold $1/8$, so that for large $S$ at most an eighth of the top-level numerators can be bad.
--
--   **Formalization Note** The statement is an `∀ᶠ S in atTop` assertion, i.e. it holds for all sufficiently large real $S$. The powers $S^{\pm1/4}$ are real powers (`Real.rpow`), $m(S)$ is `scaleM S`, $\operatorname{depth}(S)$ is `depth S` and $R$ is `descentR`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/DensityBounds.lean#L73-L106

import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SmoothBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorMoments
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeLists
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeProducts
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_HammingDistance
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SamplePartitions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ProductCorrelations
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_LevelSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListConstruction
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ScaleGeometry
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ScaleBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ResidueSystem
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TerminalScale
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DescentSets
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_MomentRecurrence

open OAI OAI.ShortEgyptian
attribute [local instance] scaleFinDecidableEq
open scoped BigOperators
open Filter Topology

theorem OAI.ShortEgyptian.eventually_density_numeric : ∀ᶠ S : ℝ in atTop,
    (depth S:ℝ)*Real.exp (2*(descentR:ℝ)*S^(1/4:ℝ)-(1/1000:ℝ)*scaleM S*S^(-(1/4:ℝ))) ≤ 1/8 := by sorry
