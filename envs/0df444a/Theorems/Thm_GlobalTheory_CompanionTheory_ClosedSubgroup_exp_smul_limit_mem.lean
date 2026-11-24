-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ClosedSubgroup_exp_smul_limit_mem
-- name    : GlobalTheory.CompanionTheory.ClosedSubgroup.exp_smul_limit_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:34:16.049074+00:00
-- url     : https://prove2.me/theorems/d6766558-acfd-42a7-948d-6630777f7a4f
-- title:
--   Closed Subgroup: exp smul limit mem
-- statement:
--   The Closed Subgroup construction uses the exp smul limit mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsSmoothLogMemLieAlg.lean#L35-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsSmoothLogMemLieAlg.lean#L35-L63

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SmComplete
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HasDerivAtExpMulExpOfFiniteDimensional
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSmoothLog
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSmoothLogMemLieAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open SmoothVectors Filter Topology
open scoped ContDiff Matrix.Norms.Elementwise
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ClosedSubgroup
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]

theorem GlobalTheory.CompanionTheory.ClosedSubgroup.exp_smul_limit_mem {G : Set A} (hc : IsClosed G) (h1 : (1 : A) ∈ G)
    (hmul : ∀ g ∈ G, ∀ h ∈ G, g * h ∈ G) {ε : ℕ → ℝ} {a : ℕ → A} {Y : A}
    (hε0 : ∀ k, 0 < ε k) (hε : Tendsto ε atTop (𝓝 0)) (ha : Tendsto a atTop (𝓝 Y))
    (hG : ∀ k, NormedSpace.exp (ε k • a k) ∈ G) {t : ℝ} (ht : 0 ≤ t) :
    NormedSpace.exp (t • Y) ∈ G := by sorry
