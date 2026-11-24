-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ComplexSets_DiscCover_cover_of_radii
-- name    : GlobalTheory.CompanionTheory.ComplexSets.DiscCover.cover_of_radii
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:33:45.161797+00:00
-- url     : https://prove2.me/theorems/13fb6eb1-af6c-4467-b08f-b94e689392fb
-- title:
--   Disc Cover: cover of radii
-- statement:
--   The Disc Cover construction uses the cover of radii property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteProjectionPushforward.lean#L76-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteProjectionPushforward.lean#L76-L179

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_AnalyticGerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteGermProjectionOpenAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermPrimitiveForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormSheetedOffDiscriminant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnbranchedProperCountConstant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCentredDiscCoverCurve
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteProjectionPushforward
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ComplexSets GlobalTheory.CompanionTheory.ComplexSets.DiscCover
open Metric

theorem GlobalTheory.CompanionTheory.ComplexSets.DiscCover.cover_of_radii (hCount : UnbranchedProperCountConstant.Statement) (σ : Type) [Fintype σ]
    (Y : Set (σ → ℂ)) (w : σ → ℂ) (A : (σ → ℂ) →L[ℂ] (Fin 1 → ℂ)) (r ρ : ℝ) (hr : 0 < r) (hρ : 0 < ρ)
    (hw : w ∈ Y) (hcomp : IsCompact (Y ∩ closedBall w r))
    (hsph : ∀ x ∈ Y, dist x w = r → A x ∉ ball (A w) ρ)
    (hiso : ∀ x ∈ Y ∩ closedBall w r, A x = A w → x = w)
    (hsheet : ∀ x ∈ Y ∩ closedBall w r, A x ≠ A w → A x ∈ ball (A w) ρ →
      ∃ (O : Set (Fin 1 → ℂ)) (V : Set (σ → ℂ)) (g : (Fin 1 → ℂ) → σ → ℂ), IsOpen O ∧ IsOpen V ∧ x ∈ V ∧
        AnalyticOnNhd ℂ g O ∧ (∀ t ∈ O, A (g t) = t) ∧ Y ∩ V = g '' O)
    (hsurj : A '' (Y ∩ ball w r) ∈ 𝓝 (A w)) :
    ∃ N : ℕ, IsCentredDiscCover (Y ∩ (ball w r ∩ A ⁻¹' ball (A w) ρ)) w
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).comp A) ρ N := by sorry
