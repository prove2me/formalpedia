-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_GramAlg_sigma_invol
-- name    : GlobalTheory.CompanionTheory.SW.GramAlg.sigma_invol
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:05:55.617826+00:00
-- url     : https://prove2.me/theorems/3a046ad6-d0af-496c-a972-0fc684510e69
-- title:
--   Gram Alg: sigma invol
-- statement:
--   The Gram Alg construction uses the sigma invol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramRightActionIdentities.lean#L44-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramRightActionIdentities.lean#L44-L48

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

theorem GlobalTheory.CompanionTheory.SW.GramAlg.sigma_invol [NumberField F] [NumberField E] {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) (x : E) :
    σ (σ x) = x := by sorry
