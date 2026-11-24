-- Prove2me | Theorems.Thm_GlobalTheory_FormalLog_om_key
-- name    : GlobalTheory.FormalLog.om_key
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:36:31.413891+00:00
-- url     : https://prove2.me/theorems/1dbff0ba-1434-442b-9192-e15f4834f889
-- title:
--   Formal Log: om key
-- statement:
--   The Formal Log construction uses the om key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalFamilyConstantCoeffZeroZeroSecondVar.lean#L150-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalFamilyConstantCoeffZeroZeroSecondVar.lean#L150-L165

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalFamilyConstantCoeffZeroZeroSecondVar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.FormalLog
variable {k : Type} [CommRing k] {d : ℕ}
variable (G : FGLaw k d)

theorem GlobalTheory.FormalLog.om_key (i a b : Fin d) :
    ∑ j, Jac G j b * pderiv k ((0 : Fin 1), a) (Om G i j) = ∑ c, pderiv k ((0 : Fin 1), c) (Om G i a) * Jac G c b := by sorry
