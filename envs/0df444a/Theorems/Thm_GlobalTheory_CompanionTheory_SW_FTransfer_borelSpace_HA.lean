-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_FTransfer_borelSpace_HA
-- name    : GlobalTheory.CompanionTheory.SW.FTransfer.borelSpace_HA
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:03:56.18538+00:00
-- url     : https://prove2.me/theorems/5dd32a59-4481-4d33-9158-3b56780b1706
-- title:
--   FTransfer: borel Space HA
-- statement:
--   The FTransfer construction uses the borel Space HA property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/FundamentalDomainTransportCongruentForm.lean#L39-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/FundamentalDomainTransportCongruentForm.lean#L39-L40

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitaryIsomOfIsometry
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FundamentalDomainTransportCongruentForm
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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FTransfer
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R]

theorem GlobalTheory.CompanionTheory.SW.FTransfer.borelSpace_HA (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    BorelSpace (HA R σ J) := by sorry
