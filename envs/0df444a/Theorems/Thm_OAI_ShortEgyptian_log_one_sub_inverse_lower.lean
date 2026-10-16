-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_log_one_sub_inverse_lower
-- name    : OAI.ShortEgyptian.log_one_sub_inverse_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:44:29.901846+00:00
-- url     : https://prove2.me/theorems/f98e8269-fa84-4af9-8030-3f45743d5850
-- title:
--   Lower bound $\log(1-1/r)\ge-2/r$ for $r\ge2$
-- statement:
--   For every real number $r\ge2$,
--
--   $$
--   \log\Big(1-\frac1r\Big)\ge-\frac2r .
--   $$
--
--   This is an elementary quantitative form of $\log(1-x)\approx-x$ for $0<x=1/r\le\tfrac12$. It is used to bound powers of $\alpha=1-1/R$ from below: for every $n\in\mathbb N$ one gets $\alpha^{n}=e^{n\log\alpha}\ge e^{-2n/R}$, which shows that $\alpha^{n}$ stays bounded away from $0$ as long as $n$ is small compared with $R$.
--
--   **Formalization Note** The logarithm is Mathlib's `Real.log`; here its argument $1-1/r$ lies in $[\tfrac12,1)$, so no convention for nonpositive arguments is involved.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/RecurrenceUnrolling.lean#L52-L65

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
open Finset Classical

theorem OAI.ShortEgyptian.log_one_sub_inverse_lower (r : ℝ) (hr : 2 ≤ r) :
    -(2/r) ≤ Real.log (1-1/r) := by sorry
