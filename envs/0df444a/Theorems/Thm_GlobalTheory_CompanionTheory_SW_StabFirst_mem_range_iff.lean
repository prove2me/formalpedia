-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_mem_range_iff
-- name    : GlobalTheory.CompanionTheory.SW.StabFirst.mem_range_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:30:35.761088+00:00
-- url     : https://prove2.me/theorems/50e045ca-0686-4dc9-9acc-79e2d67faa6a
-- title:
--   Stab First: mem range iff
-- statement:
--   The Stab First construction uses the mem range iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneRightInjective.lean#L219-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneRightInjective.lean#L219-L238

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

theorem GlobalTheory.CompanionTheory.SW.StabFirst.mem_range_iff (hs : s ≠ 0) (h : HA R σ (blockOne s J)) :
    h ∈ (iotaHom R σ J s).range ↔
      ((HA.mat R σ _ h : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) 0 0 = 1 ∧
        ∀ i : Fin M, (HA.mat R σ _ h : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) i.succ 0 = 0) := by sorry
