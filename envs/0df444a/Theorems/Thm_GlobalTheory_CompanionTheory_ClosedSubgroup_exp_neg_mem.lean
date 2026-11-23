-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ClosedSubgroup_exp_neg_mem
-- name    : GlobalTheory.CompanionTheory.ClosedSubgroup.exp_neg_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:55.537327+00:00
-- url     : https://prove2.me/theorems/0780519b-c587-4efc-a99d-6f0ef7b994f3
-- title:
--   Closed Subgroup: exp neg mem
-- statement:
--   The Closed Subgroup construction uses the exp neg mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsSmoothLogMemLieAlg.lean#L22-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsSmoothLogMemLieAlg.lean#L22-L33

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

theorem GlobalTheory.CompanionTheory.ClosedSubgroup.exp_neg_mem {G : Set A} (hinv : ∀ g ∈ G, ∃ h ∈ G, h * g = 1 ∧ g * h = 1) {x : A}
    (hx : NormedSpace.exp x ∈ G) : NormedSpace.exp (-x) ∈ G := by sorry
