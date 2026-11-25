-- Prove2me | Theorems.Thm_GlobalTheory_quad_nonneg
-- name    : GlobalTheory.quad_nonneg
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:54:30.720501+00:00
-- url     : https://prove2.me/theorems/44b61d42-e6a0-458a-bf91-4793810e8d5e
-- title:
--   Global Theory: quad nonneg
-- statement:
--   The Global Theory construction uses the quad nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsPosZsmulMemRange.lean#L27-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsPosZsmulMemRange.lean#L27-L31

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsPosZsmulMemRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory
variable {X : Type} [AddCommGroup X] {Bf : X →+ X →+ ℤ} {Q : X → ℤ}

theorem GlobalTheory.quad_nonneg (hQ : ∀ x, 2 * Q x = Bf x x) (hp : ∀ x, x ≠ 0 → 1 ≤ Q x) (x : X) :
    0 ≤ Q x := by sorry
