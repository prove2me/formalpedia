-- Prove2me | Theorems.Thm_GlobalTheory_SpecialConn_thickFib_isPullback
-- name    : GlobalTheory.SpecialConn.thickFib_isPullback
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:23:54.557568+00:00
-- url     : https://prove2.me/theorems/fcb7ab00-15b9-59f8-bce2-be85943d1437
-- title:
--   Special Conn: thick Fib is Pullback
-- statement:
--   The Special Conn construction uses the thick Fib is Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ThickFibIsPullback.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ThickFibIsPullback.lean#L29-L31

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

theorem GlobalTheory.SpecialConn.thickFib_isPullback (n : ℕ) :
    IsPullback (thickι f n) (thickStr f n) f (Spec.map (CommRingCat.ofHom (thickQ O n))) := by sorry
