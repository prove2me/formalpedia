-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_pairwise_disjoint_doubleCoset_permGL
-- name    : GroundTheory.Automorphic.pairwise_disjoint_doubleCoset_permGL
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:53:50.399981+00:00
-- url     : https://prove2.me/theorems/1f1aaf51-739f-5798-98e3-5f4da1682609
-- title:
--   Automorphic: pairwise disjoint double Coset perm GL
-- statement:
--   The Automorphic construction uses the pairwise disjoint double Coset perm GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteBruhat.lean#L331-L337
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteBruhat.lean#L331-L337

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Matrix DoubleCoset
variable {n : ℕ} {k : Type*} [Field k]

theorem GroundTheory.Automorphic.pairwise_disjoint_doubleCoset_permGL :
    Pairwise (Function.onFun Disjoint fun σ : Equiv.Perm (Fin n) =>
      doubleCoset (permGL k σ) (borel n k) (borel n k)) := by sorry
