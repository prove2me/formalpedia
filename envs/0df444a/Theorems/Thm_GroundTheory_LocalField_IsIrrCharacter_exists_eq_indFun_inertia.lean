-- Prove2me | Theorems.Thm_GroundTheory_LocalField_IsIrrCharacter_exists_eq_indFun_inertia
-- name    : GroundTheory.LocalField.IsIrrCharacter.exists_eq_indFun_inertia
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:35:14.135426+00:00
-- url     : https://prove2.me/theorems/b1f08144-b8ce-4a66-9b43-d8f91ab148dc
-- title:
--   Is Irr Character: exists eq ind Fun inertia
-- statement:
--   The Is Irr Character construction uses the exists eq ind Fun inertia property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionClifford.lean#L282-L415
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionClifford.lean#L282-L415

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionClifford
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open Module Representation
variable {G : Type*} [Group G] [Fintype G] {A : Subgroup G} [A.Normal]
open Classical

theorem GroundTheory.LocalField.IsIrrCharacter.exists_eq_indFun_inertia {χ : G → ℂ} (hχ : IsIrrCharacter χ) {θ : A → ℂ}
    (hθ : IsIrrCharacter θ) (h : charInner A (χ ∘ A.subtype) θ ≠ 0) :
    ∃ ψ : inertia A θ → ℂ, IsIrrCharacter ψ ∧ χ = indFun (inertia A θ).subtype ψ := by sorry
