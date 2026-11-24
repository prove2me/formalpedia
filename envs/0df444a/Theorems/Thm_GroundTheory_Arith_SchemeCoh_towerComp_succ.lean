-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_towerComp_succ
-- name    : GroundTheory.Arith.SchemeCoh.towerComp_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:26.300799+00:00
-- url     : https://prove2.me/theorems/6a45bc39-7034-4c5b-919c-fcd76838115d
-- title:
--   Scheme Coh: tower Comp succ
-- statement:
--   The Scheme Coh construction uses the tower Comp succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/FormalLimit.lean#L36-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/FormalLimit.lean#L36-L37

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

theorem GroundTheory.Arith.SchemeCoh.towerComp_succ (n k : ℕ) : towerComp τ n (k + 1) = (towerComp τ n k).comp (τ (n + k)) := by sorry
