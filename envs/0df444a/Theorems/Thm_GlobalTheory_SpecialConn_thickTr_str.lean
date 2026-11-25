-- Prove2me | Theorems.Thm_GlobalTheory_SpecialConn_thickTr_str
-- name    : GlobalTheory.SpecialConn.thickTr_str
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:24:25.60273+00:00
-- url     : https://prove2.me/theorems/a05a36ae-58c8-4c91-97b7-147681602bc9
-- title:
--   Special Conn: thick Tr str
-- statement:
--   The Special Conn construction uses the thick Tr str property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ThickFibIsPullback.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ThickFibIsPullback.lean#L41-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ThickFibIsPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.SpecialConn
variable {O : Type} [CommRing O] [IsLocalRing O] {Y : Scheme.{0}} (f : Y ⟶ Spec (.of O))

theorem GlobalTheory.SpecialConn.thickTr_str (n : ℕ) :
    thickTr f n ≫ thickStr f (n + 1) = thickStr f n ≫ Spec.map (CommRingCat.ofHom (thickR O n)) := by sorry
