-- Prove2me | Theorems.Thm_GlobalTheory_ActLimit_TendsS_unique
-- name    : GlobalTheory.ActLimit.TendsS.unique
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:14:00.141453+00:00
-- url     : https://prove2.me/theorems/9ddf6673-4bf1-49d0-9d22-7ee02f49790b
-- title:
--   Tends S: unique
-- statement:
--   The Tends S construction uses the unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FormalGroupActionLimitsIntegralEndomorphisms.lean#L82-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FormalGroupActionLimitsIntegralEndomorphisms.lean#L82-L84

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

theorem GlobalTheory.ActLimit.TendsS.unique {τ : Type} {f : ℕ → MvPowerSeries τ C} {g g' : MvPowerSeries τ C}
    (h : TendsS V f g) (h' : TendsS V f g') : g = g' := by sorry
