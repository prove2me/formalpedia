-- Prove2me | Theorems.Thm_GlobalTheory_ActLimit_exists_lim
-- name    : GlobalTheory.ActLimit.exists_lim
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:13:56.035805+00:00
-- url     : https://prove2.me/theorems/f87bef25-addd-4c8c-9279-51e7ede83749
-- title:
--   Act Limit: exists lim
-- statement:
--   The Act Limit construction uses the exists lim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FormalGroupActionLimitsIntegralEndomorphisms.lean#L177-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FormalGroupActionLimitsIntegralEndomorphisms.lean#L177-L181

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

theorem GlobalTheory.ActLimit.exists_lim [CharZero C] {O : Type} [CommRing O] [StarRing O] (Y : FBChart C V O dd) {a : ℕ → O}
    (ha : ActCv Y a) : ∃ e : Pt C 1 dd, ∀ i, TendsS V (fun n => Y.B.A.act (a n) i) (e i) := by sorry
