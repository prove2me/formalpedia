-- Prove2me | Theorems.Thm_GlobalTheory_T_norm_tensorProduct_map_id_right
-- name    : GlobalTheory.T.norm_tensorProduct_map_id_right
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:53:50.005188+00:00
-- url     : https://prove2.me/theorems/68eb7a74-c0f2-4af7-9638-8fadbd926110
-- title:
--   T: norm tensor Product map id right
-- statement:
--   The T construction uses the norm tensor Product map id right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/NormTensorProductMapLeftStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/NormTensorProductMapLeftStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_NormTensorProductMapLeft
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_NormTensorProductMapLeftStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.norm_tensorProduct_map_id_right : ∀ {R B L : Type} [inst : Field R] [inst_1 : CommRing B] [inst_2 : Algebra R B] [inst_3 : Field L] [inst_4 : Algebra R L] [FiniteDimensional R L] (f : B →ₐ[R] B) (w : B ⊗[R] L), Algebra.norm B (Algebra.TensorProduct.map f (AlgHom.id R L) w) = f (Algebra.norm B w) := by sorry
