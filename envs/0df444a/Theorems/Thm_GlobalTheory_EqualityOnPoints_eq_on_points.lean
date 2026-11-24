-- Prove2me | Theorems.Thm_GlobalTheory_EqualityOnPoints_eq_on_points
-- name    : GlobalTheory.EqualityOnPoints.eq_on_points
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:58:08.960462+00:00
-- url     : https://prove2.me/theorems/4f307e5a-0db5-4bb7-9dc4-c27cde978735
-- title:
--   Equality On Points: eq on points
-- statement:
--   The Equality On Points construction uses the eq on points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/EqOnPoints.lean#L7-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/EqOnPoints.lean#L7-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_EqOnPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits
open GlobalTheory GlobalTheory.EqualityOnPoints

theorem GlobalTheory.EqualityOnPoints.eq_on_points {W X Y Z : Scheme.{0}} {a b : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s]
    (h : a ≫ s = b ≫ s) (i : W ⟶ X) [IsDominant i] (hi : i ≫ a = i ≫ b) (x : X) :
    (a x : Y) = b x := by sorry
