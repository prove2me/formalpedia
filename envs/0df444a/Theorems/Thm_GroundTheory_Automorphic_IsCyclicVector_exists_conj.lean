-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsCyclicVector_exists_conj
-- name    : GroundTheory.Automorphic.IsCyclicVector.exists_conj
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:30:54.134118+00:00
-- url     : https://prove2.me/theorems/37573d3e-233f-4c30-afc6-9542b8109462
-- title:
--   Is Cyclic Vector: exists conj
-- statement:
--   The Is Cyclic Vector construction uses the exists conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjCyclic.lean#L225-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjCyclic.lean#L225-L246

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

theorem GroundTheory.Automorphic.IsCyclicVector.exists_conj {f' : Module.End E V'} {v' : V'} (hv : IsCyclicVector f v)
    (hv' : IsCyclicVector f' v') (hch : f.charpoly = f'.charpoly) :
    ∃ e : V ≃ₗ[E] V', ∀ x, e (f x) = f' (e x) := by sorry
