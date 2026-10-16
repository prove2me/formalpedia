-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_terminal_tail_subset
-- name    : OAI.ShortEgyptian.terminal_tail_subset
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:17:07.299305+00:00
-- url     : https://prove2.me/theorems/b196a48f-05ab-4605-adee-ac0d9e1cd74c
-- title:
--   The sum of $u^{-5}$ over any finite set of integers $u\ge3$ is at most $1/2$
-- statement:
--   Let $U$ be a finite set of natural numbers such that $u\ge3$ for every $u\in U$. Then
--
--   $$
--   \sum_{u\in U}\Bigl(e^{-\frac{1}{200}\log u}\Bigr)^{1000}\;\le\;\frac12 .
--   $$
--
--   Since $\bigl(e^{-\log u/200}\bigr)^{1000}=e^{-5\log u}=u^{-5}$, this is the statement $\sum_{u\in U}u^{-5}\le\frac12$.
--
--   The form of the summand matches how the lemma is used. The quantity $e^{-\log u/200}$ bounds the probability that one random list is Fourier-bad at the modulus $u$, so its $1000$-th power bounds the probability that $1000$ independent lists all fail there. The lemma shows that these failure probabilities, summed over any finite set of moduli $u\ge3$, stay below $\frac12$.
--
--   **Formalization Note** $\log$ is the natural logarithm `Real.log` applied to $u$ cast to $\mathbb{R}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/SelectionBounds.lean#L49-L62

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

open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset

theorem OAI.ShortEgyptian.terminal_tail_subset (U : Finset ℕ) (hU : ∀ u ∈ U, 3 ≤ u) :
    ∑ u ∈ U, (Real.exp (-(1/200:ℝ)*Real.log u))^1000 ≤ (1/2:ℝ) := by sorry
