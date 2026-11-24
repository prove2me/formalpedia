-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeAdj_integral_eq_sum
-- name    : GlobalTheory.CompanionTheory.HeckeAdj.integral_eq_sum
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:46:15.184678+00:00
-- url     : https://prove2.me/theorems/3777dad7-bbca-4812-abfc-c744f26fbb08
-- title:
--   Hecke Adj: integral eq sum
-- statement:
--   The Hecke Adj construction uses the integral eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteOutNeZero.lean#L36-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteOutNeZero.lean#L36-L71

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteOutNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SplitFlip
noncomputable section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeAdj
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G]

theorem GlobalTheory.CompanionTheory.HeckeAdj.integral_eq_sum (μ : Measure G) [μ.IsMulLeftInvariant] (K : Subgroup G) (hKo : IsOpen (K : Set G))
    (hfin : μ (K : Set G) ≠ ⊤) {φ : G → ℂ} (hφ : HasCompactSupport φ)
    (hr : ∀ g, ∀ k ∈ K, φ (g * k) = φ g) :
    ∫ g, φ g ∂μ = μ.real (K : Set G) • ∑ᶠ q : G ⧸ K, φ q.out := by sorry
