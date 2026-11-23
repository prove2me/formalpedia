-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_exists_borel_of_isUpperTriangular
-- name    : GroundTheory.Automorphic.exists_borel_of_isUpperTriangular
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:47.896273+00:00
-- url     : https://prove2.me/theorems/2f3c5ff8-d4c8-4d8a-812f-3518039c8c2d
-- title:
--   Automorphic: exists borel of is Upper Triangular
-- statement:
--   The Automorphic construction uses the exists borel of is Upper Triangular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteBruhat.lean#L61-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteBruhat.lean#L61-L71

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

theorem GroundTheory.Automorphic.exists_borel_of_isUpperTriangular (M : Matrix (Fin n) (Fin n) k)
    (hM : M.IsUpperTriangular) (hd : ∀ i, M i i ≠ 0) :
    ∃ b ∈ borel n k, (b : Matrix (Fin n) (Fin n) k) = M := by sorry
