-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_map_mem_coinvariantsKer
-- name    : GroundTheory.Automorphic.map_mem_coinvariantsKer
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:55:34.969547+00:00
-- url     : https://prove2.me/theorems/41beaaf6-7816-5364-a882-b625fff8e242
-- title:
--   Automorphic: map mem coinvariants Ker
-- statement:
--   The Automorphic construction uses the map mem coinvariants Ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteLengthSubquotient.lean#L190-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteLengthSubquotient.lean#L190-L201

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
omit [TopologicalSpace G]

theorem GroundTheory.Automorphic.map_mem_coinvariantsKer {π : Representation ℂ G W} (p : Representation.IntertwiningMap ρ π)
    (N : Subgroup G) {x : V} (hx : x ∈ Representation.Coinvariants.ker (ρ.comp N.subtype)) :
    p x ∈ Representation.Coinvariants.ker (π.comp N.subtype) := by sorry
