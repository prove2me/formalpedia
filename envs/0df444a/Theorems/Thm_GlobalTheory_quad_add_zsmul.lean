-- Prove2me | Theorems.Thm_GlobalTheory_quad_add_zsmul
-- name    : GlobalTheory.quad_add_zsmul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:50:18.530479+00:00
-- url     : https://prove2.me/theorems/434be07d-8d2a-4ec0-9316-a303e654a7a6
-- title:
--   Global Theory: quad add zsmul
-- statement:
--   The Global Theory construction uses the quad add zsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsPosZsmulMemRange.lean#L11-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsPosZsmulMemRange.lean#L11-L20

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

theorem GlobalTheory.quad_add_zsmul (hs : ∀ x y, Bf x y = Bf y x) (hQ : ∀ x, 2 * Q x = Bf x x)
    (y w : X) (t : ℤ) : Q (y + t • w) = Q y + t * Bf y w + t ^ 2 * Q w := by sorry
