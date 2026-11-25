-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_mem_maxCompact_indefiniteUnitary
-- name    : GroundTheory.Automorphic.mem_maxCompact_indefiniteUnitary
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:26:52.346911+00:00
-- url     : https://prove2.me/theorems/ccc483e8-45c2-4d8d-8c4b-30e39d35db62
-- title:
--   Automorphic: mem max Compact indefinite Unitary
-- statement:
--   The Automorphic construction uses the mem max Compact indefinite Unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/CartanBasis.lean#L354-L386
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/CartanBasis.lean#L354-L386

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
open NormedSpace
open scoped Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem GroundTheory.Automorphic.mem_maxCompact_indefiniteUnitary {p q : ℕ} {g : indefiniteUnitaryGroup p q} :
    g ∈ maxCompact (indefiniteUnitaryGroup p q) ↔
      ((g : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) ∈
          Matrix.unitaryGroup (Fin p ⊕ Fin q) ℂ ∧
        ((g : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₂ = 0 ∧
        ((g : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₂₁ = 0 := by sorry
