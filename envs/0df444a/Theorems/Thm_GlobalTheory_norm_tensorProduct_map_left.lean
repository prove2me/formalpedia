-- Prove2me | Theorems.Thm_GlobalTheory_norm_tensorProduct_map_left
-- name    : GlobalTheory.norm_tensorProduct_map_left
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:13:02.746783+00:00
-- url     : https://prove2.me/theorems/cb301fd9-28bb-487d-970d-d49ddae3dfee
-- title:
--   Global Theory: norm tensor Product map left
-- statement:
--   The Global Theory construction uses the norm tensor Product map left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/NormTensorProductMapLeft.lean#L6-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/NormTensorProductMapLeft.lean#L6-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_NormTensorProductMapLeft
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory

theorem GlobalTheory.norm_tensorProduct_map_left {R B L : Type} [Field R] [CommRing B] [Algebra R B] [Field L]
    [Algebra R L] [FiniteDimensional R L] (f : B →ₐ[R] B) (w : B ⊗[R] L) :
    Algebra.norm B (Algebra.TensorProduct.map f (AlgHom.id R L) w) = f (Algebra.norm B w) := by sorry
