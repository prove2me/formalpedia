-- Prove2me | Theorems.Thm_GlobalTheory_ActLimit_tends_comp1
-- name    : GlobalTheory.ActLimit.tends_comp1
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:14:11.544118+00:00
-- url     : https://prove2.me/theorems/749cfd7f-fb77-4ce9-8e66-b5e076425350
-- title:
--   Act Limit: tends comp1
-- statement:
--   The Act Limit construction uses the tends comp1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FormalGroupActionLimitsIntegralEndomorphisms.lean#L158-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FormalGroupActionLimitsIntegralEndomorphisms.lean#L158-L162

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

theorem GlobalTheory.ActLimit.tends_comp1 {n : ℕ} {φ : ℕ → Pt C 1 dd} {e : Pt C 1 dd} (h : ∀ i, TendsS V (fun k => φ k i) (e i))
    {a : Pt C n dd} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin dd) :
    TendsS V (fun k => comp1 (φ k) a i) (comp1 e a i) := by sorry
