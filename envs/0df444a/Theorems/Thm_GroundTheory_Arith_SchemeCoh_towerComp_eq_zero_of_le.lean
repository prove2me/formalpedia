-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_towerComp_eq_zero_of_le
-- name    : GroundTheory.Arith.SchemeCoh.towerComp_eq_zero_of_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:29:20.35388+00:00
-- url     : https://prove2.me/theorems/7b587cb9-1141-403a-9d60-e2063b3d795c
-- title:
--   Scheme Coh: tower Comp eq zero of le
-- statement:
--   The Scheme Coh construction uses the tower Comp eq zero of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/FormalLimit.lean#L59-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/FormalLimit.lean#L59-L65

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

theorem GroundTheory.Arith.SchemeCoh.towerComp_eq_zero_of_le {c : ℕ} (hc : ∀ n, towerComp τ n c = 0) (n j : ℕ) :
    towerComp τ n (c + j) = 0 := by sorry
