-- Prove2me | Theorems.Thm_GlobalTheory_tmul_one_mem_nonZeroDivisors_of_flat
-- name    : GlobalTheory.tmul_one_mem_nonZeroDivisors_of_flat
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:23:46.648713+00:00
-- url     : https://prove2.me/theorems/d8026c7d-bca3-4212-aef6-29dc099c9ff9
-- title:
--   Global Theory: tmul one mem non Zero Divisors of flat
-- statement:
--   The Global Theory construction uses the tmul one mem non Zero Divisors of flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsIsMaximalTensorProductOfIsLocalHom.lean#L32-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsIsMaximalTensorProductOfIsLocalHom.lean#L32-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsIsMaximalTensorProductOfIsLocalHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory

theorem GlobalTheory.tmul_one_mem_nonZeroDivisors_of_flat (O A B : Type*) [CommRing O] [CommRing A]
    [CommRing B] [IsDomain A] [Algebra O A] [Algebra O B] [Module.Flat O B] {a : A} (ha : a ≠ 0) :
    (a ⊗ₜ[O] (1 : B)) ∈ nonZeroDivisors (A ⊗[O] B) := by sorry
