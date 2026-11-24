-- Prove2me | Theorems.Thm_GlobalTheory_JR_LinDesc_map_pair_selfDual
-- name    : GlobalTheory.JR.LinDesc.map_pair_selfDual
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:35:01.860647+00:00
-- url     : https://prove2.me/theorems/3abf32b5-0ff2-42a2-b9ba-9778fb2e074b
-- title:
--   Lin Desc: map pair self Dual
-- statement:
--   The Lin Desc construction uses the map pair self Dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PartialFourierGlOrbitEqFourierEtaleKProd.lean#L11-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PartialFourierGlOrbitEqFourierEtaleKProd.lean#L11-L78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierGlOrbitEqFourierEtaleKProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.LinDesc

theorem GlobalTheory.JR.LinDesc.map_pair_selfDual {F : Type} [NontriviallyNormedField F] [LocallyCompactSpace F] [MeasurableSpace F]
    [BorelSpace F] {r : ℕ} {V : Type} [AddCommGroup V] [Module F V] [TopologicalSpace V] [IsModuleTopology F V]
    [IsTopologicalAddGroup V] [ContinuousSMul F V] [MeasurableSpace V] [BorelSpace V]
    (ψ : AddChar F ℂ) (B : V → V → F) (hBs : ∀ x y, B x y = B y x)
    (e₁ e₂ : V ≃ₗ[F] (Fin r → F)) (hB : ∀ x y, e₁ x ⬝ᵥ e₂ y = B x y)
    (μV : Measure V) (hV : SelfDual μV (fun x y => ψ (B x y)))
    (ν : Measure (Fin r → F)) (hν : SelfDual ν (fun x y => ψ (x ⬝ᵥ y)))
    (h₀ : (Fin r → F) → ℂ) (ht₀ : IsTest h₀) (h₀0 : h₀ 0 = 1) :
    ∃ c₁ c₂ : ℂ, (∀ φ : (Fin r → F) → ℂ, ∫ x, φ (e₁ x) ∂μV = c₁ * ∫ y, φ y ∂ν) ∧
      (∀ φ : (Fin r → F) → ℂ, ∫ x, φ (e₂ x) ∂μV = c₂ * ∫ y, φ y ∂ν) ∧ c₁ * c₂ = 1 := by sorry
