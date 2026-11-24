-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_exists_linearIndependent_pow_apply_of_isAlgClosed
-- name    : GroundTheory.Automorphic.exists_linearIndependent_pow_apply_of_isAlgClosed
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:34:48.443593+00:00
-- url     : https://prove2.me/theorems/7ac884bd-13fc-4d5e-b611-d3468d861671
-- title:
--   Automorphic: exists linear Independent pow apply of is Alg Closed
-- statement:
--   The Automorphic construction uses the exists linear Independent pow apply of is Alg Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjCyclic.lean#L12-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjCyclic.lean#L12-L53

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjCyclic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Polynomial Module Matrix
variable {K W : Type*} [Field K] [IsAlgClosed K] [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

theorem GroundTheory.Automorphic.exists_linearIndependent_pow_apply_of_isAlgClosed (f : Module.End K W)
    (hf : f.charpoly.Separable) :
    ∃ w : W, LinearIndependent K (fun k : Fin (finrank K W) => (f ^ (k : ℕ)) w) := by sorry
