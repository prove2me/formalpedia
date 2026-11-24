-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_wedgeT_tmul_add_swap
-- name    : GlobalTheory.CompanionTheory.WedgeOf.wedgeT_tmul_add_swap
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:33:55.116022+00:00
-- url     : https://prove2.me/theorems/439cc5db-adb6-4bec-b1c6-0f3168e81939
-- title:
--   Wedge Of: wedge T tmul add swap
-- statement:
--   The Wedge Of construction uses the wedge T tmul add swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeOfSymmetricTensorZero.lean#L21-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeOfSymmetricTensorZero.lean#L21-L26

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IotaQInjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeOfSymmetricTensorZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeOf
variable {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V]

theorem GlobalTheory.CompanionTheory.WedgeOf.wedgeT_tmul_add_swap (a b : V) :
    wedgeT (R := R) V (a ⊗ₜ[R] b) + wedgeT (R := R) V (b ⊗ₜ[R] a) = 0 := by sorry
