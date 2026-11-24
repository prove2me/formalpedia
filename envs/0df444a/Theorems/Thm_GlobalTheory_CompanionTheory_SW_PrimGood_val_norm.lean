-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimGood_val_norm
-- name    : GlobalTheory.CompanionTheory.SW.PrimGood.val_norm
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:09:06.513106+00:00
-- url     : https://prove2.me/theorems/0722a7fc-65e1-483c-9572-61ed4ec523b4
-- title:
--   Prim Good: val norm
-- statement:
--   The Prim Good construction uses the val norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/PrimitiveVectorLatticeRescaleAlmostAll.lean#L16-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/PrimitiveVectorLatticeRescaleAlmostAll.lean#L16-L54

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IntegralAlmostAllPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_PrimitiveVectorLatticeRescaleAlmostAll
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PrimGood
variable {L Γ : Type} [Field L] [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ)

theorem GlobalTheory.CompanionTheory.SW.PrimGood.val_norm (hsq : ∀ x : L, w (x - 1) < 1 → IsSquare x) {Δ : L} (hΔ : w Δ = 1)
    (hn : ¬ IsSquare Δ) (a c : L) : w (a ^ 2 - Δ * c ^ 2) = max (w a) (w c) ^ 2 := by sorry
