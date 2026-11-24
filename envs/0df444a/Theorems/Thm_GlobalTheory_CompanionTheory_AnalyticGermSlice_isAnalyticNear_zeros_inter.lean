-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticGermSlice_isAnalyticNear_zeros_inter
-- name    : GlobalTheory.CompanionTheory.AnalyticGermSlice.isAnalyticNear_zeros_inter
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:18:54.048615+00:00
-- url     : https://prove2.me/theorems/5ad9b189-5866-4027-9394-3066ea502965
-- title:
--   Analytic Germ Slice: is Analytic Near zeros inter
-- statement:
--   The Analytic Germ Slice construction uses the is Analytic Near zeros inter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AnalyticGermFiniteProjection.lean#L11-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AnalyticGermFiniteProjection.lean#L11-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_AnalyticGerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermFiniteProjection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteGermProjectionOpenAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AnalyticGermFiniteProjection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AnalyticGermSlice

theorem GlobalTheory.CompanionTheory.AnalyticGermSlice.isAnalyticNear_zeros_inter {σ : Type} [Fintype σ] {X : Set (σ → ℂ)} {w : σ → ℂ}
    (hX : IsAnalyticNear X w) {m : ℕ} (g : Fin m → (σ → ℂ) → ℂ)
    (hg : ∀ i, AnalyticOnNhd ℂ (g i) Set.univ) :
    IsAnalyticNear {z | z ∈ X ∧ ∀ i, g i z = 0} w := by sorry
