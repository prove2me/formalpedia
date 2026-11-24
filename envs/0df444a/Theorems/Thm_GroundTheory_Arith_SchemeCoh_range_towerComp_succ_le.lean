-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_range_towerComp_succ_le
-- name    : GroundTheory.Arith.SchemeCoh.range_towerComp_succ_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:28:59.838795+00:00
-- url     : https://prove2.me/theorems/e14d619d-f3a2-43d1-a16a-939c011a748b
-- title:
--   Scheme Coh: range tower Comp succ le
-- statement:
--   The Scheme Coh construction uses the range tower Comp succ le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/FormalLimit.lean#L48-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/FormalLimit.lean#L48-L51

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

theorem GroundTheory.Arith.SchemeCoh.range_towerComp_succ_le (n k : ℕ) :
    LinearMap.range (towerComp τ n (k + 1)) ≤ LinearMap.range (towerComp τ n k) := by sorry
