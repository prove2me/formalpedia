-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_exists_KAK
-- name    : GroundTheory.Automorphic.exists_KAK
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:59.88924+00:00
-- url     : https://prove2.me/theorems/07558b37-a448-45d5-a410-8492bb8236b2
-- title:
--   Automorphic: exists KAK
-- statement:
--   The Automorphic construction uses the exists KAK property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/RealGroupsKAK.lean#L11-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/RealGroupsKAK.lean#L11-L24

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsPolar
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsKAK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Matrix Polynomial
open scoped MatrixOrder ComplexOrder
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

theorem GroundTheory.Automorphic.exists_KAK (g : GL n 𝕜) :
    ∃ k₁ k₂ : unitaryGroup n 𝕜, ∃ a : n → ℝ, (∀ i, 0 < a i) ∧
      (g : Matrix n n 𝕜) = (k₁ : Matrix n n 𝕜) * diagonal (fun i => (a i : 𝕜)) * k₂ := by sorry
