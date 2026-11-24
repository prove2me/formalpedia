-- Prove2me | Theorems.Thm_GlobalTheory_PrimitiveUnitProduct_appTop_comp_apply
-- name    : GlobalTheory.PrimitiveUnitProduct.appTop_comp_apply
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:55:39.873804+00:00
-- url     : https://prove2.me/theorems/496f8b61-b24c-49bc-bf4d-06e1988b51e9
-- title:
--   Primitive Unit Product: app Top comp apply
-- statement:
--   The Primitive Unit Product construction uses the app Top comp apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/UnitOnProductEqOne.lean#L250-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/UnitOnProductEqOne.lean#L250-L252

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnitOnProductEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct CategoryTheory AlgebraicGeometry Limits
open GlobalTheory GlobalTheory.PrimitiveUnitProduct

theorem GlobalTheory.PrimitiveUnitProduct.appTop_comp_apply {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (s : Γ(Z, ⊤)) :
    (f ≫ g).appTop s = f.appTop (g.appTop s) := by sorry
