-- Prove2me | Theorems.Thm_GlobalTheory_exists_iso_pull_cancel
-- name    : GlobalTheory.exists_iso_pull_cancel
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:36:28.38602+00:00
-- url     : https://prove2.me/theorems/c2ec265c-89c8-441d-8ec6-2192115f5a28
-- title:
--   Global Theory: exists iso pull cancel
-- statement:
--   The Global Theory construction uses the exists iso pull cancel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsIsoPullCancel.lean#L12-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsIsoPullCancel.lean#L12-L19

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsIsoPullCancel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.exists_iso_pull_cancel {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} (hL : L.IsLB)
    (hL' : L'.IsLB) (hL'' : L''.IsLB) {φ₁ : X'' ⟶ X} {φ₂ : X' ⟶ X} {θ : X'' ⟶ X'} (h : θ ≫ φ₂ = φ₁)
    (w₁ : LB.Iso L'' (L.pull φ₁)) (w₂ : LB.Iso L' (L.pull φ₂)) (g₁ : w₁.IsGen) (g₂ : w₂.IsGen) :
    ∃ (wθ : LB.Iso L'' (L'.pull θ)) (w₁' : LB.Iso L'' (L.pull (θ ≫ φ₂))),
      wθ.IsGen ∧ HEq w₁' w₁ ∧ Tri w₂ wθ w₁' := by sorry
