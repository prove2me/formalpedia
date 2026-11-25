-- Prove2me | Theorems.Thm_GlobalTheory_ActLimit_constantCoeff_germEvalTwo_eq_zero
-- name    : GlobalTheory.ActLimit.constantCoeff_germEvalTwo_eq_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:13:52.741683+00:00
-- url     : https://prove2.me/theorems/505f7be3-e96a-4260-af3b-5376441e6299
-- title:
--   Act Limit: constant Coeff germ Eval Two eq zero
-- statement:
--   The Act Limit construction uses the constant Coeff germ Eval Two eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FormalGroupActionLimitsIntegralEndomorphisms.lean#L164-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FormalGroupActionLimitsIntegralEndomorphisms.lean#L164-L167

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

theorem GlobalTheory.ActLimit.constantCoeff_germEvalTwo_eq_zero {n : ℕ} {a b : Pt C n dd} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) {f : PS C 2 dd} (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (ev ![a, b] f) = 0 := by sorry
