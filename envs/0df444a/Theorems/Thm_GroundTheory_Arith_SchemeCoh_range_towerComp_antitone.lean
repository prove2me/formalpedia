-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_range_towerComp_antitone
-- name    : GroundTheory.Arith.SchemeCoh.range_towerComp_antitone
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:52:50.52961+00:00
-- url     : https://prove2.me/theorems/97290b2e-08d8-4b53-92d2-79c4575b94e5
-- title:
--   Scheme Coh: range tower Comp antitone
-- statement:
--   The Scheme Coh construction uses the range tower Comp antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/FormalLimit.lean#L53-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/FormalLimit.lean#L53-L57

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

theorem GroundTheory.Arith.SchemeCoh.range_towerComp_antitone (n : ℕ) {k l : ℕ} (h : k ≤ l) :
    LinearMap.range (towerComp τ n l) ≤ LinearMap.range (towerComp τ n k) := by sorry
