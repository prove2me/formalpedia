-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_sum_odd_sq_mod_eight
-- name    : OAI.CirculantHadamard.sum_odd_sq_mod_eight
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:29:03.435028+00:00
-- url     : https://prove2.me/theorems/aa936250-8356-4217-81cf-358873a64a9f
-- title:
--   A sum of odd squares is its number of terms modulo eight
-- statement:
--   Let $s$ be a finite index set and $a_i\in\mathbb Z$ odd for every $i\in s$. Then
--   $$
--   \sum_{i\in s}a_i^2\equiv|s|\pmod 8 .
--   $$
--
--   This is the basic obstruction modulo eight used to exclude the remaining dyadic orders.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/ModEight.lean#L34-L49

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

open OAI OAI.CirculantHadamard
universe uIota
open scoped BigOperators

theorem OAI.CirculantHadamard.sum_odd_sq_mod_eight {ι : Type uIota} (s : Finset ι) (a : ι → ℤ)
    (ha : ∀ i ∈ s, Odd (a i)) :
    Int.ModEq 8 (∑ i ∈ s, a i ^ 2) (s.card : ℤ) := by sorry
