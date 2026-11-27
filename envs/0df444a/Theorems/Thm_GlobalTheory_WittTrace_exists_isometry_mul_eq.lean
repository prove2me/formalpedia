-- Prove2me | Theorems.Thm_GlobalTheory_WittTrace_exists_isometry_mul_eq
-- name    : GlobalTheory.WittTrace.exists_isometry_mul_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:43:12.772801+00:00
-- url     : https://prove2.me/theorems/8f9914ed-b4e4-44e4-a391-f63867545b42
-- title:
--   Witt Trace: exists isometry mul eq
-- statement:
--   The Witt Trace construction uses the exists isometry mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsIsometryOfLinearIndependent.lean#L160-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsIsometryOfLinearIndependent.lean#L160-L234

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryOfLinearIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.WittTrace
open Module Matrix GlobalTheory.HermDiag GlobalTheory.HermWitt

theorem GlobalTheory.WittTrace.exists_isometry_mul_eq (K : Type) [Field K] [StarRing K] (θ : K) (hθ : θ + star θ = 1)
    (n a : ℕ) (J : Matrix (Fin n) (Fin n) K) (X Y : Matrix (Fin n) (Fin a) K) (hJ : Jᴴ = J)
    (hdet : IsUnit J.det) (hX : X.rank = a) (hY : Y.rank = a)
    (hXY : Xᴴ * J * X = Yᴴ * J * Y) :
    ∃ g : Matrix (Fin n) (Fin n) K, gᴴ * J * g = J ∧ g * X = Y := by sorry
