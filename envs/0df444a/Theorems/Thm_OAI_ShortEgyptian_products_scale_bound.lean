-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_products_scale_bound
-- name    : OAI.ShortEgyptian.products_scale_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:23:14.075776+00:00
-- url     : https://prove2.me/theorems/76f5ebd3-0459-4c39-9fe7-e400fdbf7304
-- title:
--   A product of at most $S/\log S$ integers, each at most $2S^{100}$, is at most $e^{101S}$
-- statement:
--   Let $J$ be a finite set and let $S$ be a real number with $S\ge2$ and $\log S>0$, such that $|J|\le S/\log S$. If $a\colon J\to\mathbb{N}$ satisfies $a_j\le 2S^{100}$ for every $j\in J$, then
--
--   $$
--   \prod_{j\in J}a_j\;\le\;e^{101S} .
--   $$
--
--   The lemma bounds the size of products of $\lfloor S/\log S\rfloor$ numbers of size at most $2S^{100}$, such as the primes used to build the lists in the construction. For example, it gives the bound $t_i\le e^{101S}$ on the entries of the deterministic subset-product list, which the mean-square equidistribution estimate requires, and it is used to bound the common auxiliary denominator.
--
--   **Formalization Note** The product is computed in $\mathbb{N}$ and then cast to $\mathbb{R}$. The hypothesis $\log S>0$ already follows from $S\ge2$ but is stated separately.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/ListConstruction.lean#L82-L98

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

open OAI OAI.ShortEgyptian
universe uJ uA uR
open scoped BigOperators
open Finset Classical

theorem OAI.ShortEgyptian.products_scale_bound {J : Type uJ} [Fintype J]
    (S : ℝ) (hS : 2 ≤ S) (hlog : 0 < Real.log S)
    (hm : (Fintype.card J:ℝ) ≤ S/Real.log S)
    (a : J → ℕ) (ha : ∀ j, (a j:ℝ) ≤ 2*S^100) :
    ((∏ j,a j : ℕ):ℝ) ≤ Real.exp (101*S) := by sorry
