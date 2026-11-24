-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_exists_linearIndependent_pow_apply
-- name    : GroundTheory.Automorphic.exists_linearIndependent_pow_apply
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:34:53.539386+00:00
-- url     : https://prove2.me/theorems/fc4562fc-0eda-4672-94b5-7608c973f17c
-- title:
--   Automorphic: exists linear Independent pow apply
-- statement:
--   The Automorphic construction uses the exists linear Independent pow apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjCyclic.lean#L120-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjCyclic.lean#L120-L158

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
variable {E V : Type*} [Field E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]

theorem GroundTheory.Automorphic.exists_linearIndependent_pow_apply [Infinite E] (f : Module.End E V)
    (hf : f.charpoly.Separable) :
    ∃ v : V, LinearIndependent E (fun k : Fin (finrank E V) => (f ^ (k : ℕ)) v) := by sorry
