-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsSubquotient_of_injective
-- name    : GroundTheory.Automorphic.IsSubquotient.of_injective
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:56:02.851105+00:00
-- url     : https://prove2.me/theorems/1e204cc4-4941-48ff-b0c4-e3c7310265c9
-- title:
--   Is Subquotient: of injective
-- statement:
--   The Is Subquotient construction uses the of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteLengthSubquotient.lean#L57-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteLengthSubquotient.lean#L57-L59

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
variable {G : Type*} [Group G] {V W U : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W] [AddCommGroup U] [Module ℂ U]
variable {π : Representation ℂ G W} {ρ : Representation ℂ G V} {θ : Representation ℂ G U}

theorem GroundTheory.Automorphic.IsSubquotient.of_injective (i : Representation.IntertwiningMap π ρ) (hi : Injective i) :
    IsSubquotient π ρ := by sorry
