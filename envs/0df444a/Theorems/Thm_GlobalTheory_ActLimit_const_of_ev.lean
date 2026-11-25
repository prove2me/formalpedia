-- Prove2me | Theorems.Thm_GlobalTheory_ActLimit_const_of_ev
-- name    : GlobalTheory.ActLimit.const_of_ev
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:14:15.877238+00:00
-- url     : https://prove2.me/theorems/054ab7b2-6dc6-4ab0-9019-fec6e6f9cfe1
-- title:
--   Act Limit: const of ev
-- statement:
--   The Act Limit construction uses the const of ev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FormalGroupActionLimitsIntegralEndomorphisms.lean#L141-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FormalGroupActionLimitsIntegralEndomorphisms.lean#L141-L148

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
variable {dd : ℕ}

theorem GlobalTheory.ActLimit.const_of_ev {m n : ℕ} {a : Fin m → Pt C n dd} (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0)
    {f : PS C m dd} (hf : ev a f = 0) : MvPowerSeries.constantCoeff f = 0 := by sorry
