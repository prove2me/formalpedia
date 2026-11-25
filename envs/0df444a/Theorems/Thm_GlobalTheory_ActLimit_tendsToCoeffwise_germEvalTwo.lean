-- Prove2me | Theorems.Thm_GlobalTheory_ActLimit_tendsToCoeffwise_germEvalTwo
-- name    : GlobalTheory.ActLimit.tendsToCoeffwise_germEvalTwo
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:14:31.662802+00:00
-- url     : https://prove2.me/theorems/368e4746-77e3-4f8b-8d43-57dea16c26eb
-- title:
--   Act Limit: tends To Coeffwise germ Eval Two
-- statement:
--   The Act Limit construction uses the tends To Coeffwise germ Eval Two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FormalGroupActionLimitsIntegralEndomorphisms.lean#L169-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FormalGroupActionLimitsIntegralEndomorphisms.lean#L169-L175

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

theorem GlobalTheory.ActLimit.tendsToCoeffwise_germEvalTwo {n : ℕ} {a b : ℕ → Pt C n dd} {a' b' : Pt C n dd}
    (ha : ∀ k i, MvPowerSeries.constantCoeff (a k i) = 0) (hb : ∀ k i, MvPowerSeries.constantCoeff (b k i) = 0)
    (ha' : ∀ i, TendsS V (fun k => a k i) (a' i)) (hb' : ∀ i, TendsS V (fun k => b k i) (b' i)) (f : PS C 2 dd) :
    TendsS V (fun k => ev ![a k, b k] f) (ev ![a', b'] f) := by sorry
