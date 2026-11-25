-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_aeval_apply_eq_sum_modByMonic
-- name    : GroundTheory.Automorphic.aeval_apply_eq_sum_modByMonic
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:34:37.04111+00:00
-- url     : https://prove2.me/theorems/2511f69b-f5dc-4912-bf83-7ce4ec39d96b
-- title:
--   Automorphic: aeval apply eq sum mod By Monic
-- statement:
--   The Automorphic construction uses the aeval apply eq sum mod By Monic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjCyclic.lean#L210-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjCyclic.lean#L210-L223

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
variable {E V V' : Type*} [Field E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  [AddCommGroup V'] [Module E V'] [FiniteDimensional E V']
variable {f : Module.End E V} {v : V}

theorem GroundTheory.Automorphic.aeval_apply_eq_sum_modByMonic (f : Module.End E V) (v : V) (p : E[X]) :
    aeval f p v = ∑ k : Fin (finrank E V), (p %ₘ f.charpoly).coeff k • (f ^ (k : ℕ)) v := by sorry
