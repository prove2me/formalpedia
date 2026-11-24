-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_GramAlg_sigR_invol
-- name    : GlobalTheory.CompanionTheory.SW.GramAlg.sigR_invol
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:05:20.004326+00:00
-- url     : https://prove2.me/theorems/5cb89e13-fb85-4749-a1db-58ca57fe9c8c
-- title:
--   Gram Alg: sig R invol
-- statement:
--   The Gram Alg construction uses the sig R invol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramRightActionIdentities.lean#L52-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramRightActionIdentities.lean#L52-L57

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramRightActionIdentities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GramAlg
variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R]

theorem GlobalTheory.CompanionTheory.SW.GramAlg.sigR_invol {σ : E →ₐ[F] E} (h : ∀ x, σ (σ x) = x) (x : R ⊗[F] E) :
    sigR R σ (sigR R σ x) = x := by sorry
