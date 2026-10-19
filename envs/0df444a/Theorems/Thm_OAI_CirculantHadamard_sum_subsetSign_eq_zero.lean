-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_sum_subsetSign_eq_zero
-- name    : OAI.CirculantHadamard.sum_subsetSign_eq_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:41:20.306042+00:00
-- url     : https://prove2.me/theorems/87ab2cea-52ce-4f2d-9980-deafa669f366
-- title:
--   Alternating signs over all subsets sum to zero
-- statement:
--   Let $t$ be a nonempty finite set. Then
--   $$
--   \sum_{S\subseteq t}(-1)^{|S|}=0 .
--   $$
--
--   This is the binomial identity $(1-1)^{|t|}=0$ for $|t|\ge1$; it shows that an alternating product over the subsets of $t$ has as many factors with exponent $+1$ as with exponent $-1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/AlternatingProducts.lean#L44-L63

import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalDVR
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_IntegerTwoLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicPolynomial
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedConjugation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicIntegerEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_DyadicRemainder
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedEisenstein
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_OrderHalving
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryBlocks
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryCoefficients
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicRings
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_PrimeComponents
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_PrimeCharacterEvaluations
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalizationMaps
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalization
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_AlternatingProducts

open OAI OAI.CirculantHadamard
universe uI uG uH
open scoped BigOperators
variable {I : Type uI}

theorem OAI.CirculantHadamard.sum_subsetSign_eq_zero (t : Finset I) (ht : t.Nonempty) :
    ∑ S ∈ t.powerset, subsetSign S = 0 := by sorry
