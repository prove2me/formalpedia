-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_mem_borel_iff
-- name    : GroundTheory.Automorphic.mem_borel_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:47.164331+00:00
-- url     : https://prove2.me/theorems/acd17128-53d8-4a4d-a85a-cf9fc5fb0899
-- title:
--   Automorphic: mem borel iff
-- statement:
--   The Automorphic construction uses the mem borel iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteBruhat.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteBruhat.lean#L27-L29

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

theorem GroundTheory.Automorphic.mem_borel_iff (g : GL (Fin n) k) :
    g ∈ borel n k ↔ ∀ i j : Fin n, j < i → (g : Matrix (Fin n) (Fin n) k) i j = 0 := by sorry
