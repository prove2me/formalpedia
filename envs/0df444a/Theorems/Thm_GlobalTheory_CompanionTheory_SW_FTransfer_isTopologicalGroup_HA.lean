-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_FTransfer_isTopologicalGroup_HA
-- name    : GlobalTheory.CompanionTheory.SW.FTransfer.isTopologicalGroup_HA
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:03:51.081803+00:00
-- url     : https://prove2.me/theorems/4f09447c-8c1c-41de-90ef-2f2e6d55cb4e
-- title:
--   FTransfer: is Topological Group HA
-- statement:
--   The FTransfer construction uses the is Topological Group HA property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/FundamentalDomainTransportCongruentForm.lean#L34-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/FundamentalDomainTransportCongruentForm.lean#L34-L37

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

theorem GlobalTheory.CompanionTheory.SW.FTransfer.isTopologicalGroup_HA [IsTopologicalRing R] [Module.Finite F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) : IsTopologicalGroup (HA R σ J) := by sorry
