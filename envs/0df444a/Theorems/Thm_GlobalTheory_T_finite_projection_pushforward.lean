-- Prove2me | Theorems.Thm_GlobalTheory_T_finite_projection_pushforward
-- name    : GlobalTheory.T.finite_projection_pushforward
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:31:31.791007+00:00
-- url     : https://prove2.me/theorems/895b13ed-908a-492c-b84f-342a4dc5c44b
-- title:
--   T: finite projection pushforward
-- statement:
--   The T construction uses the finite projection pushforward property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteProjectionPushforwardStatement.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteProjectionPushforwardStatement.lean#L11-L12

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteProjectionPushforward
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_AnalyticGerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteGermProjectionOpenAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermPrimitiveForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormSheetedOffDiscriminant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnbranchedProperCountConstant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCentredDiscCoverCurve
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteProjectionPushforwardStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finite_projection_pushforward : FiniteGermProjectionOpenAt.Statement → IrreducibleGermPrimitiveForm.Statement → PrimitiveFormSheetedOffDiscriminant.Statement → UnbranchedProperCountConstant.Statement → ∀ (σ : Type) [Fintype σ] (Y : Set (σ → ℂ)) (w : σ → ℂ) (A : (σ → ℂ) →L[ℂ] (Fin 1 → ℂ)), IsAnalyticNear Y w → GermIrreducibleAt Y w → (∃ W' ∈ 𝓝 w, ∀ x ∈ Y ∩ W', A x = A w → x = w) → (∀ h : (Fin 1 → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ Y → h (A z) = 0) → ∀ᶠ y in 𝓝 (A w), h y = 0) → ∃ (Y' : Set (σ → ℂ)) (p : (σ → ℂ) →L[ℂ] ℂ) (ρ : ℝ) (N : ℕ), Y' ⊆ Y ∧ IsCentredDiscCover Y' w p ρ N := by sorry
