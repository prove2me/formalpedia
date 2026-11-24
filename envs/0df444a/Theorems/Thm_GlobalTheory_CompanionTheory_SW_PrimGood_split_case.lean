-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimGood_split_case
-- name    : GlobalTheory.CompanionTheory.SW.PrimGood.split_case
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:08:40.148299+00:00
-- url     : https://prove2.me/theorems/88e538d6-6556-4189-8c50-a3b18ca6366d
-- title:
--   Prim Good: split case
-- statement:
--   The Prim Good construction uses the split case property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/PrimitiveVectorLatticeRescaleAlmostAll.lean#L242-L347
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/PrimitiveVectorLatticeRescaleAlmostAll.lean#L242-L347

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
variable {L K : Type} [Field L] [CommRing K] [Algebra L K] (B : Module.Basis (Fin 2) L K)
variable {B} {Δ : L}
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ)

theorem GlobalTheory.CompanionTheory.SW.PrimGood.split_case (h0 : B 0 = 1) (h1 : B 1 * B 1 = algebraMap L K Δ)
    (h2 : w (2 : L) = 1) (hΔ : w Δ = 1) {s : L} (hs : s * s = Δ)
    {M : ℕ} (y z : Fin M → K) (hz : z ⬝ᵥ y = 1) :
    ∃ (u : Kˣ) (z' : Fin M → K), (∀ k l, w (B.repr ((u : K) * y k) l) ≤ 1) ∧
      (∀ k l, w (B.repr (z' k) l) ≤ 1) ∧ ∑ k, z' k * ((u : K) * y k) = 1 := by sorry
