-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_CayleyCase_kapSum_withG
-- name    : GlobalTheory.UnitLemma.CayleyCase.kapSum_withG
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:50:31.953565+00:00
-- url     : https://prove2.me/theorems/0e84cbaa-ab3d-46ef-9617-acf957cbc95e
-- title:
--   Cayley Case: kap Sum with G
-- statement:
--   The Cayley Case construction uses the kap Sum with G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitLemmaResiduallyUnipotentViaCayley.lean#L246-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitLemmaResiduallyUnipotentViaCayley.lean#L246-L251

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardStableLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinEqTopAndIsReducedOfCharpolySeparableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyMulLeftSeparableOfAdjoinEqTopStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaResiduallyUnipotentViaCayley
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.CayleyCase
variable {K : UQ}

theorem GlobalTheory.UnitLemma.CayleyCase.kapSum_withG (B₁ B₂ : InvAlg K) (Y₁ : B₁.A) (Y₂ : B₂.A)
    (h : ∀ L : Submodule K.O (B₁.A × B₂.A), (∀ y ∈ L, (B₁.g, B₂.g) * y ∈ L) ↔ (∀ y ∈ L, (Y₁, Y₂) * y ∈ L)) :
    InvAlg.kapSum (withG B₁ Y₁) (withG B₂ Y₂) = InvAlg.kapSum B₁ B₂ := by sorry
