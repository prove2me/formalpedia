-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_SemilinearResidue_linearIndependent_of_notMem_span
-- name    : GroundTheory.PAdicHodge.SemilinearResidue.linearIndependent_of_notMem_span
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:45:21.181411+00:00
-- url     : https://prove2.me/theorems/18a2ab32-8285-44cc-b2fb-2afe4be27e61
-- title:
--   Semilinear Residue: linear Independent of not Mem span
-- statement:
--   The Semilinear Residue construction uses the linear Independent of not Mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SemilinearResidue.lean#L89-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SemilinearResidue.lean#L89-L99

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_SemilinearResidue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial Module Finset
open GroundTheory.PAdicHodge.SemilinearResidue
variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

theorem GroundTheory.PAdicHodge.SemilinearResidue.linearIndependent_of_notMem_span (v : ℕ → V) : ∀ m : ℕ,
    (∀ j < m, v j ∉ Submodule.span k (Set.range (fun i : Fin j => v i))) →
      LinearIndependent k (fun i : Fin m => v i)
  := by sorry
