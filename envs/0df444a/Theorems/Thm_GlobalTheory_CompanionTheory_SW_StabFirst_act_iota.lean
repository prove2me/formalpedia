-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_act_iota
-- name    : GlobalTheory.CompanionTheory.SW.StabFirst.act_iota
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:09:51.241816+00:00
-- url     : https://prove2.me/theorems/51ab4f87-fda8-4fa2-b30d-b31029cc6fb6
-- title:
--   Stab First: act iota
-- statement:
--   The Stab First construction uses the act iota property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneRightInjective.lean#L268-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneRightInjective.lean#L268-L277

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneRightInjective
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.StabFirst
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (s : E)

theorem GlobalTheory.CompanionTheory.SW.StabFirst.act_iota {n : ℕ} (u : HA R σ J) (X : Fin n → Fin M → R ⊗[F] E) :
    actW R σ _ (iotaHom R σ J s u) (consTup X) = consTup (actW R σ J u X) := by sorry
