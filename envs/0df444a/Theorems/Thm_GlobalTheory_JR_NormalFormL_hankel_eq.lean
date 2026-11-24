-- Prove2me | Theorems.Thm_GlobalTheory_JR_NormalFormL_hankel_eq
-- name    : GlobalTheory.JR.NormalFormL.hankel_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:49.402074+00:00
-- url     : https://prove2.me/theorems/45905c90-a2c2-4016-a8d4-73f7b4af1b47
-- title:
--   Normal Form L: hankel eq
-- statement:
--   The Normal Form L construction uses the hankel eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisBorderedMatrixNormalFormInvariants.lean#L143-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisBorderedMatrixNormalFormInvariants.lean#L143-L148

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariants
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.NormalFormL
variable {k : Type} [Field k] {r : ℕ}

theorem GlobalTheory.JR.NormalFormL.hankel_eq (Y : Gl r k) : Cm Y * Bm Y = hankel (inv Y) := by sorry
