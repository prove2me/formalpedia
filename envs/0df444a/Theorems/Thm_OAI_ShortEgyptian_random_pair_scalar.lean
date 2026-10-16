-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_random_pair_scalar
-- name    : OAI.ShortEgyptian.random_pair_scalar
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:09:11.450436+00:00
-- url     : https://prove2.me/theorems/447ef988-6ef4-4a48-855d-1f124efa85df
-- title:
--   Exponential inequality for the pair-correlation error terms when $\log u\ge 40$
-- statement:
--   Let $u$ be a natural number with $\log u\ge40$, where $\log$ is the natural logarithm. Then
--
--   $$
--   \frac{e}{\bigl(e^{(\log u)/10}\bigr)^{3/4}}+\sqrt u\;e^{-\frac7{10}\log u}\ \le\ e^{-\frac1{20}\log u}+e^{-\frac15\log u}.
--   $$
--
--   Equivalently, $e\,u^{-3/40}+u^{-1/5}\le u^{-1/20}+u^{-1/5}$. This is the numerical step that turns the pair-correlation bound $M/G^a+\sqrt u\,B$, evaluated at $M=e$, $G=e^{V/10}$, $a=3/4$ and $B=e^{-7V/10}$ with $V=\log u$, into the error $e^{-V/20}+e^{-V/5}$.
--
--   **Formalization Note** In Lean $\log 0=0$, so the hypothesis $\log u\ge40$ also forces $u>0$. The power $3/4$ is a real power (`Real.rpow`).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/RandomBounds.lean#L184-L200

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

theorem OAI.ShortEgyptian.random_pair_scalar (u : ℕ) (hV : 40 ≤ Real.log u) :
    Real.exp 1/(Real.exp (Real.log u/10))^(3/4:ℝ)+
      Real.sqrt u*Real.exp (-(7/10:ℝ)*Real.log u) ≤
      Real.exp (-(1/20:ℝ)*Real.log u)+Real.exp (-(1/5:ℝ)*Real.log u) := by sorry
