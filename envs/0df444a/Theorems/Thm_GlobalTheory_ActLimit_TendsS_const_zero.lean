-- Prove2me | Theorems.Thm_GlobalTheory_ActLimit_TendsS_const_zero
-- name    : GlobalTheory.ActLimit.TendsS.const_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:16:16.330233+00:00
-- url     : https://prove2.me/theorems/87cbedf3-7c53-4d62-a15a-f5b08fc2d4d6
-- title:
--   Tends S: const zero
-- statement:
--   The Tends S construction uses the const zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FormalGroupActionLimitsIntegralEndomorphisms.lean#L86-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FormalGroupActionLimitsIntegralEndomorphisms.lean#L86-L90

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalGroupActionLimitsIntegralEndomorphisms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Formalism.L2.FormalSeriesBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.ActLimit
variable {C : Type} [Field C] {V : VF C}

theorem GlobalTheory.ActLimit.TendsS.const_zero {τ : Type} {f : ℕ → MvPowerSeries τ C} {g : MvPowerSeries τ C}
    (h : TendsS V f g) (hf : ∀ n, MvPowerSeries.constantCoeff (f n) = 0) : MvPowerSeries.constantCoeff g = 0 := by sorry
