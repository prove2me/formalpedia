-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_bijective_mk_permGL
-- name    : GroundTheory.Automorphic.bijective_mk_permGL
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:53:24.981906+00:00
-- url     : https://prove2.me/theorems/83cd52f1-9768-5139-9b2c-3aed98aa69be
-- title:
--   Automorphic: bijective mk perm GL
-- statement:
--   The Automorphic construction uses the bijective mk perm GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteBruhat.lean#L339-L350
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteBruhat.lean#L339-L350

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

theorem GroundTheory.Automorphic.bijective_mk_permGL :
    Function.Bijective fun σ : Equiv.Perm (Fin n) =>
      DoubleCoset.mk (borel n k) (borel n k) (permGL k σ) := by sorry
