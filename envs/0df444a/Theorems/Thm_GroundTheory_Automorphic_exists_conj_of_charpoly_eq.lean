-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_exists_conj_of_charpoly_eq
-- name    : GroundTheory.Automorphic.exists_conj_of_charpoly_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:53:26.412006+00:00
-- url     : https://prove2.me/theorems/054a808e-79c5-5093-a7e6-789c07b1950e
-- title:
--   Automorphic: exists conj of charpoly eq
-- statement:
--   The Automorphic construction uses the exists conj of charpoly eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjCyclic.lean#L248-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjCyclic.lean#L248-L253

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

theorem GroundTheory.Automorphic.exists_conj_of_charpoly_eq [Infinite E] {f f' : Module.End E V}
    (hf : f.charpoly.Separable) (hch : f.charpoly = f'.charpoly) :
    ∃ e : V ≃ₗ[E] V, ∀ x, e (f x) = f' (e x) := by sorry
