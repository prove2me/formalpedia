-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsSubquotient_of_injective_of_surjective
-- name    : GroundTheory.Automorphic.IsSubquotient.of_injective_of_surjective
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:55:51.0108+00:00
-- url     : https://prove2.me/theorems/3adf61af-2310-4cd1-80b4-de73aa559889
-- title:
--   Is Subquotient: of injective of surjective
-- statement:
--   The Is Subquotient construction uses the of injective of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteLengthSubquotient.lean#L30-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteLengthSubquotient.lean#L30-L51

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

theorem GroundTheory.Automorphic.IsSubquotient.of_injective_of_surjective {X : Type*} [AddCommGroup X] [Module ℂ X]
    {α : Representation ℂ G X} (i : Representation.IntertwiningMap α ρ) (hi : Injective i)
    (q : Representation.IntertwiningMap α π) (hq : Surjective q) : IsSubquotient π ρ := by sorry
