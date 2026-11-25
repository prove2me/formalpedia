-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_exists_cartanBasis
-- name    : GroundTheory.Automorphic.exists_cartanBasis
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:24:52.746864+00:00
-- url     : https://prove2.me/theorems/1de948d9-5ee6-4aa9-a40d-b2468b062818
-- title:
--   Automorphic: exists cartan Basis
-- statement:
--   The Automorphic construction uses the exists cartan Basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/CartanBasis.lean#L199-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/CartanBasis.lean#L199-L259

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_CartanBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Matrix
set_option linter.unusedSectionVars false
attribute [local instance 100] LieRing.ofAssociativeRing
variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (L : LieSubalgebra ℝ (Matrix ι ι 𝕜))
variable {L}

theorem GroundTheory.Automorphic.exists_cartanBasis (hstar : ∀ X ∈ L, Xᴴ ∈ L) :
    ∃ (d : ℕ) (b : Module.Basis (Fin d) ℝ L) (ε : Fin d → ℝ), (∀ i, ε i = 1 ∨ ε i = -1) ∧
      (∀ i j, traceForm L (b i) (b j) = if i = j then ε i else 0) ∧
      ∀ i, ε i = -1 → ((b i : Matrix ι ι 𝕜))ᴴ = -(b i : Matrix ι ι 𝕜) := by sorry
