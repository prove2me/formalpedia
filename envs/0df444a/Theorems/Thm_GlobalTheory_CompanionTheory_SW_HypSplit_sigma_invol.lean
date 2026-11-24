-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_HypSplit_sigma_invol
-- name    : GlobalTheory.CompanionTheory.SW.HypSplit.sigma_invol
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:06:51.412832+00:00
-- url     : https://prove2.me/theorems/201016f5-4678-46b2-a005-d693bf63d5a9
-- title:
--   Hyp Split: sigma invol
-- statement:
--   The Hyp Split construction uses the sigma invol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/IsotropicVectorSplitsHyperbolicPlane.lean#L176-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/IsotropicVectorSplitsHyperbolicPlane.lean#L176-L180

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IsotropicVectorSplitsHyperbolicPlane
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HypSplit

theorem GlobalTheory.CompanionTheory.SW.HypSplit.sigma_invol {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (a : E) : σ (σ a) = a := by sorry
