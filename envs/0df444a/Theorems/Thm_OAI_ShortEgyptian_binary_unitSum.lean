-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_binary_unitSum
-- name    : OAI.ShortEgyptian.binary_unitSum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:34:59.080491+00:00
-- url     : https://prove2.me/theorems/3e8113bc-f6d1-4ec3-9cc8-98b3d89fb8be
-- title:
--   Writing $u/M$ with $u\le2^a$ and $2^a\mid M$ as a sum of at most $a+1$ unit fractions
-- statement:
--   **Theorem.** Let $a,M,u$ be natural numbers with $M>0$, $2^a\mid M$ and $u\le2^a$. Then there are positive integers $n_1,\dots,n_L$ (possibly $L=0$) such that
--
--   $$\frac{u}{M}=\sum_{i=1}^{L}\frac{1}{n_i}\qquad\text{and}\qquad L\le a+1 .$$
--
--   The denominators are not claimed to be distinct or at least $2$; when $u<M$ the latter is automatic. The lemma is the final step of the construction of short Egyptian fraction expansions: once a numerator has been reduced below a power of two dividing the common denominator, it is written with a number of unit fractions that is logarithmic in that power of two.
--
--   **Formalization Note** The conclusion is stated for a list `ns : List ℕ` with all entries positive, `unitSum ns = u/M` in $\mathbb{Q}$ and `ns.length ≤ a+1`, where `unitSum ns` is the sum of the reciprocals of the entries of `ns`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/TerminalExpansion.lean#L25-L49

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

open OAI OAI.ShortEgyptian
attribute [local instance] scaleFinDecidableEq
open scoped BigOperators
open Finset Classical

theorem OAI.ShortEgyptian.binary_unitSum (a M u : ℕ) (hM : 0 < M) (hd : 2^a ∣ M) (hu : u ≤ 2^a) :
    ∃ ns : List ℕ, (∀ n ∈ ns, 0 < n) ∧ unitSum ns = (u:ℚ)/M ∧ ns.length ≤ a+1 := by sorry
