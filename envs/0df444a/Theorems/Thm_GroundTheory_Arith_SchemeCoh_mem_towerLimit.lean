-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_mem_towerLimit
-- name    : GroundTheory.Arith.SchemeCoh.mem_towerLimit
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:52:30.666476+00:00
-- url     : https://prove2.me/theorems/fc0b0b07-41c7-4092-92c7-73d826d6a2ea
-- title:
--   Scheme Coh: mem tower Limit
-- statement:
--   The Scheme Coh construction uses the mem tower Limit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/FormalLimit.lean#L27-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/FormalLimit.lean#L27-L28

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_FormalLimit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
universe u
noncomputable section
variable {A : Type u} [CommRing A] {E : ℕ → Type u} [∀ n, AddCommGroup (E n)]
  [∀ n, Module A (E n)] (τ : ∀ n, E (n + 1) →ₗ[A] E n)

theorem GroundTheory.Arith.SchemeCoh.mem_towerLimit (x : ∀ n, E n) : x ∈ towerLimit τ ↔ ∀ n, τ n (x (n + 1)) = x n := by sorry
