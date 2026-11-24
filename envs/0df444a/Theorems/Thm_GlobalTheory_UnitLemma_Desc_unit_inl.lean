-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Desc_unit_inl
-- name    : GlobalTheory.UnitLemma.Desc.unit_inl
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:27:14.354799+00:00
-- url     : https://prove2.me/theorems/3e781291-1ae7-4f4e-9dce-bdfcb9e1bc55
-- title:
--   Desc: unit inl
-- statement:
--   The Desc construction uses the unit inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsUniformizerIdempotentFrameProd.lean#L94-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsUniformizerIdempotentFrameProd.lean#L94-L101

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsUniformizerIdempotentFrameProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc

theorem GlobalTheory.UnitLemma.Desc.unit_inl {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] (σ₁ : R₁ ≃+* R₁) (σ₂ : R₂ ≃+* R₂)
    (x e : R₁) (hu : IsUnit x) (hσ : σ₁ x = x) (h1 : x * (1 - e) = 1 - e) :
    (IsUnit ((x, 1) : R₁ × R₂) ∧ RingEquiv.prodCongr σ₁ σ₂ (x, 1) = (x, 1)) ∧
      ((x, 1) : R₁ × R₂) * (1 - (e, 0)) = 1 - (e, 0) := by sorry
