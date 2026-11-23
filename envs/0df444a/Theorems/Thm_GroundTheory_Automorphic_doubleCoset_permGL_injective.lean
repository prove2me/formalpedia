-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_doubleCoset_permGL_injective
-- name    : GroundTheory.Automorphic.doubleCoset_permGL_injective
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:54.115259+00:00
-- url     : https://prove2.me/theorems/94b6bda0-7838-4dd0-aec0-b418002bfd29
-- title:
--   Automorphic: double Coset perm GL injective
-- statement:
--   The Automorphic construction uses the double Coset perm GL injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteBruhat.lean#L312-L320
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteBruhat.lean#L312-L320

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

theorem GroundTheory.Automorphic.doubleCoset_permGL_injective {σ τ : Equiv.Perm (Fin n)} {g : GL (Fin n) k}
    (hσ : g ∈ doubleCoset (permGL k σ) (borel n k) (borel n k))
    (hτ : g ∈ doubleCoset (permGL k τ) (borel n k) (borel n k)) : σ = τ := by sorry
