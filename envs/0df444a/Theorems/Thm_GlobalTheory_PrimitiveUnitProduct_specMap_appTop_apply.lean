-- Prove2me | Theorems.Thm_GlobalTheory_PrimitiveUnitProduct_specMap_appTop_apply
-- name    : GlobalTheory.PrimitiveUnitProduct.specMap_appTop_apply
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:55:15.238345+00:00
-- url     : https://prove2.me/theorems/fa681152-f49d-488f-8ea8-2d77b3ee6cc0
-- title:
--   Primitive Unit Product: spec Map app Top apply
-- statement:
--   The Primitive Unit Product construction uses the spec Map app Top apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/UnitOnProductEqOne.lean#L254-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/UnitOnProductEqOne.lean#L254-L256

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

theorem GlobalTheory.PrimitiveUnitProduct.specMap_appTop_apply {R S : CommRingCat} (φ : R ⟶ S) (s : Γ(Spec R, ⊤)) :
    (Scheme.ΓSpecIso S).hom ((Spec.map φ).appTop s) = φ ((Scheme.ΓSpecIso R).hom s) := by sorry
