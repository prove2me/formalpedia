-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HasFiniteLength_wellFoundedGT
-- name    : GroundTheory.Automorphic.HasFiniteLength.wellFoundedGT
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:57.361987+00:00
-- url     : https://prove2.me/theorems/0e31b66e-8756-4769-b22a-8f1ba5b8cef2
-- title:
--   Has Finite Length: well Founded GT
-- statement:
--   The Has Finite Length construction uses the well Founded GT property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteLengthLattice.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteLengthLattice.lean#L32-L34

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteLengthLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Function
variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {ρ : Representation ℂ G V}

theorem GroundTheory.Automorphic.HasFiniteLength.wellFoundedGT (h : HasFiniteLength ρ) :
    WellFoundedGT (Subrepresentation ρ) := by sorry
