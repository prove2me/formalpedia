-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_mem_HFin_iff
-- name    : GlobalTheory.CompanionTheory.SW.StabFirst.mem_HFin_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:09:26.074798+00:00
-- url     : https://prove2.me/theorems/5453bd6f-7bee-4343-b316-b8774f686a08
-- title:
--   Stab First: mem HFin iff
-- statement:
--   The Stab First construction uses the mem HFin iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneRightInjective.lean#L240-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneRightInjective.lean#L240-L266

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

theorem GlobalTheory.CompanionTheory.SW.StabFirst.mem_HFin_iff (hs : s ≠ 0) (u : HA R σ J) :
    HA.mat R σ _ (iotaHom R σ J s u) ∈ HFin R σ (blockOne s J) ↔ HA.mat R σ J u ∈ HFin R σ J := by sorry
