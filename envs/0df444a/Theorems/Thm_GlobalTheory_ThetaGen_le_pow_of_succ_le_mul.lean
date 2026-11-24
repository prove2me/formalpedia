-- Prove2me | Theorems.Thm_GlobalTheory_ThetaGen_le_pow_of_succ_le_mul
-- name    : GlobalTheory.ThetaGen.le_pow_of_succ_le_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:05:55.576882+00:00
-- url     : https://prove2.me/theorems/905979f7-0569-4c54-817a-2fee26548f8f
-- title:
--   Theta Gen: le pow of succ le mul
-- statement:
--   The Theta Gen construction uses the le pow of succ le mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsIsHomogeneousOfMemSpanPow.lean#L159-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsIsHomogeneousOfMemSpanPow.lean#L159-L182

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIsHomogeneousOfMemSpanPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.ThetaGen
variable {X : Type}
variable (R : ℕ → Submodule ℂ (X → ℂ))

theorem GlobalTheory.ThetaGen.le_pow_of_succ_le_mul (hmul : ∀ a b, R a * R b ≤ R (a + b)) {e : ℕ} (h1e : 1 ≤ e)
    (he : ∀ d, e ≤ d → R (d + 1) ≤ R 1 * R d) (j : ℕ) : R (e * (j + 1)) ≤ R e ^ (j + 1) := by sorry
