-- Prove2me | Theorems.Thm_GlobalTheory_exists_fourier_expansion_tube
-- name    : GlobalTheory.exists_fourier_expansion_tube
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:32:39.121995+00:00
-- url     : https://prove2.me/theorems/3c4ed509-613a-49d0-a23e-d7480eb63e49
-- title:
--   Global Theory: exists fourier expansion tube
-- statement:
--   The Global Theory construction uses the exists fourier expansion tube property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsFourierExpansionHolomorphicTube.lean#L78-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsFourierExpansionHolomorphicTube.lean#L78-L279

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_NormLeTsumOfCubeFourierCoeffLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsFourierExpansionHolomorphicTube
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory
open MeasureTheory
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real Classical
open MeasureTheory

theorem GlobalTheory.exists_fourier_expansion_tube :
    ∀ (ι : Type) [Fintype ι] (Ω : Set (ι → ℝ)) (f : (ι → ℂ) → ℂ), IsOpen Ω → Convex ℝ Ω →
      DifferentiableOn ℂ f {z | (fun i => (z i).im) ∈ Ω} →
      (∀ z, (fun i => (z i).im) ∈ Ω → ∀ m : ι → ℤ, f (z + fun i => (m i : ℂ)) = f z) →
      ∃ a : (ι → ℤ) → ℂ, (∀ z, (fun i => (z i).im) ∈ Ω →
        HasSum (fun ν : ι → ℤ => a ν * cexp (2 * π * I * ∑ i, (ν i : ℂ) * z i)) (f z)) ∧
        ∀ y ∈ Ω, ∀ ν : ι → ℤ, a ν = ∫ x in Set.pi Set.univ (fun _ : ι => Set.Ico (0 : ℝ) 1),
          f (fun i => (x i : ℂ) + I * y i) *
            cexp (-(2 * π * I * ∑ i, (ν i : ℂ) * ((x i : ℂ) + I * y i))) := by sorry
