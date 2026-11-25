-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_agreement_iff_guarded
-- name    : GlobalTheory.CompanionTheory.Ar.PB.agreement_iff_guarded
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:00:05.162367+00:00
-- url     : https://prove2.me/theorems/d8b84f77-8be6-577b-b4f2-123cf1b3bdda
-- title:
--   PB: agreement iff guarded
-- statement:
--   The PB construction uses the agreement iff guarded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Statements/MetricStatements/AgreementIffGuarded.lean#L52-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Statements/MetricStatements/AgreementIffGuarded.lean#L52-L59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FlagIndices_InstFintypeFlIdx
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_GeometricAbelianConnected
import Definitions.Def_Development_AutomorphicSpectrum_Statements_MetricStatements_AgreementIffGuarded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Filter Topology
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem GlobalTheory.CompanionTheory.Ar.PB.agreement_iff_guarded : Agreement ↔
  (Inputs → ∀ (D : ℕ) (σ : Type) [Fintype σ] (S : AnSys D σ) (abelian₂ : ℝ), 0 < S.t₀ → ∃ C₃ s₀ : ℝ, 0 < s₀ ∧
    ∀ (II : IntersectionSystem), IsFullIntersectionSystem II →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (Re : Realis S P),
      (∀ w, Tendsto (fun t => Re.num II t w) (𝓝[>] 0) (𝓝 (Re.limNum II w))) ∧
      ∀ s, 0 < s → s ≤ s₀ → Real.exp (-(s ^ 2)⁻¹) ≤ S.t₀ ∧ ∀ c : σ → ℝ, ∑ a, |c a| ≤ abelian₂ →
        |eval c (Re.FT II (Real.exp (-(s ^ 2)⁻¹))) - eval c (Re.PB II)| ≤ C₃ * s) := by sorry
