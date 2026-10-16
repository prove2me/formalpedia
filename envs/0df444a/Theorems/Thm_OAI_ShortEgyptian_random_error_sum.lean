-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_random_error_sum
-- name    : OAI.ShortEgyptian.random_error_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:08:20.463524+00:00
-- url     : https://prove2.me/theorems/d267a688-807b-4cdb-90ca-9972224d69e7
-- title:
--   Three exponential error terms sum to at most $e^{-\min(m,V)/100}$
-- statement:
--   Let $m$ and $V$ be real numbers with $\min(m,V)\ge100$. Then
--
--   $$
--   e^{-m/16}+e^{-V/20}+e^{-V/5}\ \le\ e^{-\min(m,V)/100}.
--   $$
--
--   This collects the three error terms of the second-moment argument for random subset products, namely the Hamming-tail term $e^{-m/16}$ and the two terms of the pair-correlation bound, into a single exponential in $\min(m,V)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/RandomBounds.lean#L123-L140

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

open OAI OAI.ShortEgyptian
universe uJ uA
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

theorem OAI.ShortEgyptian.random_error_sum (m V : ℝ) (hw : 100 ≤ min m V) :
    Real.exp (-m/16)+Real.exp (-(1/20:ℝ)*V)+Real.exp (-(1/5:ℝ)*V) ≤
      Real.exp (-(1/100:ℝ)*min m V) := by sorry
