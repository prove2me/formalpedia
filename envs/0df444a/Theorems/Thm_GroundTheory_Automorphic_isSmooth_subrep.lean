-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_isSmooth_subrep
-- name    : GroundTheory.Automorphic.isSmooth_subrep
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:01:46.982952+00:00
-- url     : https://prove2.me/theorems/6a2b2492-2c63-45ec-b1dc-a0bea2e59505
-- title:
--   Automorphic: is Smooth subrep
-- statement:
--   The Automorphic construction uses the is Smooth subrep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteLengthSubquotient.lean#L205-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteLengthSubquotient.lean#L205-L210

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteLengthLattice
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteLengthSubquotient
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
open Function Parabolic
universe u
variable {G : Type*} [Group G] [TopologicalSpace G] {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G V}
variable [IsTopologicalGroup G]

theorem GroundTheory.Automorphic.isSmooth_subrep (hρ : IsSmooth ρ) (C : Subrepresentation ρ) :
    IsSmooth C.toRepresentation := by sorry
