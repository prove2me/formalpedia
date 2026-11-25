-- Prove2me | Theorems.Thm_GlobalTheory_ActLimit_TendsS_subst
-- name    : GlobalTheory.ActLimit.TendsS.subst
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:14:29.279848+00:00
-- url     : https://prove2.me/theorems/6a5b0ce5-c288-470d-b537-d8cd5d7897cd
-- title:
--   Tends S: subst
-- statement:
--   The Tends S construction uses the subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FormalGroupActionLimitsIntegralEndomorphisms.lean#L101-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FormalGroupActionLimitsIntegralEndomorphisms.lean#L101-L115

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

theorem GlobalTheory.ActLimit.TendsS.subst {σ τ : Type} [Finite σ] {a : ℕ → σ → MvPowerSeries τ C} {b : σ → MvPowerSeries τ C}
    (ha : ∀ n s, MvPowerSeries.constantCoeff (a n s) = 0) (hab : ∀ s, TendsS V (fun n => a n s) (b s))
    {f : ℕ → MvPowerSeries σ C} {g : MvPowerSeries σ C} (h : TendsS V f g) :
    TendsS V (fun n => MvPowerSeries.subst (a n) (f n)) (MvPowerSeries.subst b g) := by sorry
