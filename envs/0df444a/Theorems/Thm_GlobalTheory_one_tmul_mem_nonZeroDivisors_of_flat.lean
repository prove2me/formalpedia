-- Prove2me | Theorems.Thm_GlobalTheory_one_tmul_mem_nonZeroDivisors_of_flat
-- name    : GlobalTheory.one_tmul_mem_nonZeroDivisors_of_flat
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:13:24.43246+00:00
-- url     : https://prove2.me/theorems/6796a588-fbde-451a-8129-3ce614ddf399
-- title:
--   Global Theory: one tmul mem non Zero Divisors of flat
-- statement:
--   The Global Theory construction uses the one tmul mem non Zero Divisors of flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsIsMaximalTensorProductOfIsLocalHom.lean#L17-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsIsMaximalTensorProductOfIsLocalHom.lean#L17-L30

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

theorem GlobalTheory.one_tmul_mem_nonZeroDivisors_of_flat (O A B : Type*) [CommRing O] [CommRing A]
    [CommRing B] [IsDomain B] [Algebra O A] [Algebra O B] [Module.Flat O A] {b : B} (hb : b ≠ 0) :
    ((1 : A) ⊗ₜ[O] b) ∈ nonZeroDivisors (A ⊗[O] B) := by sorry
