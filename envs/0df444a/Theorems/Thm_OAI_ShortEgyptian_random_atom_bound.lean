-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_random_atom_bound
-- name    : OAI.ShortEgyptian.random_atom_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:07:36.23653+00:00
-- url     : https://prove2.me/theorems/48f8ad60-0448-49b7-821f-f26d84f9e7cc
-- title:
--   Atom bound $s^s/P^s\le e^{-7V/10}$ for $P\ge S^{99}$
-- statement:
--   Let $S,V,P$ be real numbers and $s$ a natural number such that $S\ge2$, $P\ge S^{99}$, $s\le S$ and
--   $$s\ge\frac{V}{140\log S}.$$
--   Then
--
--   $$
--   \frac{s^{s}}{P^{s}}\ \le\ e^{-7V/10}.
--   $$
--
--   With $P=|A|$ the number of available primes and $s$ the number of fresh coordinates, the left side is the atom bound $s^s/|A|^s$, an upper bound for the probability that a product of $s$ independent random primes takes any prescribed value. The inequality shows that this probability is exponentially small in $V$.
--
--   **Formalization Note** Powers are natural-number powers; for $s=0$ the left side is $1$, and the hypothesis then forces $V\le0$. The denominator is positive since $P\ge S^{99}>0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/RandomBounds.lean#L82-L105

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

theorem OAI.ShortEgyptian.random_atom_bound (S V P : ℝ) (s : ℕ) (hS : 2 ≤ S)
    (hP : S^99 ≤ P) (hsS : (s:ℝ) ≤ S) (hs : V/(140*Real.log S) ≤ (s:ℝ)) :
    (s:ℝ)^s/P^s ≤ Real.exp (-(7/10:ℝ)*V) := by sorry
