-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Desc_isFrame_prod
-- name    : GlobalTheory.UnitLemma.Desc.isFrame_prod
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:27:31.423589+00:00
-- url     : https://prove2.me/theorems/ce7e5470-d99a-4e2e-9422-e3fd40bedb52
-- title:
--   Desc: is Frame prod
-- statement:
--   The Desc construction uses the is Frame prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsUniformizerIdempotentFrameProd.lean#L112-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsUniformizerIdempotentFrameProd.lean#L112-L134

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

theorem GlobalTheory.UnitLemma.Desc.isFrame_prod : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂] (e₁ π₁ : ι₁ → B₁.A) (e₂ π₂ : ι₂ → B₂.A) (S₁ : Finset ι₁) (S₂ : Finset ι₂), IsFrame B₁ e₁ π₁ S₁ → IsFrame B₂ e₂ π₂ S₂ → IsFrame (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A))) (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A))) (S₁.disjSum S₂) := by sorry
