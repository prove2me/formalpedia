-- Prove2me | Theorems.Thm_GlobalTheory_ActLimit_TendsS_sub
-- name    : GlobalTheory.ActLimit.TendsS.sub
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:16:17.937493+00:00
-- url     : https://prove2.me/theorems/301987b5-90a7-4a61-a555-010e33c9b6c6
-- title:
--   Tends S: sub
-- statement:
--   The Tends S construction uses the sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FormalGroupActionLimitsIntegralEndomorphisms.lean#L78-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FormalGroupActionLimitsIntegralEndomorphisms.lean#L78-L80

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalGroupActionLimitsIntegralEndomorphisms
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sub
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sub

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

theorem GlobalTheory.ActLimit.TendsS.sub {τ : Type} {f f' : ℕ → MvPowerSeries τ C} {g g' : MvPowerSeries τ C}
    (h : TendsS V f g) (h' : TendsS V f' g') : TendsS V (fun n => f n - f' n) (g - g') := by sorry
