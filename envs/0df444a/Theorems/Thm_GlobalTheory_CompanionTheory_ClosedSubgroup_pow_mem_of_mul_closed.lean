-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ClosedSubgroup_pow_mem_of_mul_closed
-- name    : GlobalTheory.CompanionTheory.ClosedSubgroup.pow_mem_of_mul_closed
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:33:47.614177+00:00
-- url     : https://prove2.me/theorems/cdaa048b-7c71-4311-b6c5-4c8423fc3ef4
-- title:
--   Closed Subgroup: pow mem of mul closed
-- statement:
--   The Closed Subgroup construction uses the pow mem of mul closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsSmoothLogMemLieAlg.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsSmoothLogMemLieAlg.lean#L16-L20

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

theorem GlobalTheory.CompanionTheory.ClosedSubgroup.pow_mem_of_mul_closed {G : Set A} (h1 : (1 : A) ∈ G) (hmul : ∀ g ∈ G, ∀ h ∈ G, g * h ∈ G)
    {g : A} (hg : g ∈ G) (m : ℕ) : g ^ m ∈ G := by sorry
