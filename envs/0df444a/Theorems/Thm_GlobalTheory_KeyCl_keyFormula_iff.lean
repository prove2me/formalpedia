-- Prove2me | Theorems.Thm_GlobalTheory_KeyCl_keyFormula_iff
-- name    : GlobalTheory.KeyCl.keyFormula_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:13:32.091134+00:00
-- url     : https://prove2.me/theorems/70d3a030-daa2-473d-9e98-1c1b44a1b73b
-- title:
--   Key Cl: key Formula iff
-- statement:
--   The Key Cl construction uses the key Formula iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/KeyFormula/KeyRootOfKeyFormula.lean#L71-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/KeyFormula/KeyRootOfKeyFormula.lean#L71-L85

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRootOfKeyFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.KeyCl
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.KeyCl.keyFormula_iff :
    KeyFormula ↔ ∃ κ : Rule, Homog (fun _ => 1) κ ∧ Funct κ ∧ UnitSp κ ∧ ThetaOne κ ∧ ArchNorm (fun _ => 1) κ := by sorry
