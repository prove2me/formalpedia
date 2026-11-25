-- Prove2me | Theorems.Thm_GlobalTheory_Height_OrderTieGuards_v_zpow
-- name    : GlobalTheory.Height.OrderTieGuards.v_zpow
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T02:43:28.066495+00:00
-- url     : https://prove2.me/theorems/c0e2499d-30c1-44da-9fe7-c106e107e6ca
-- title:
--   Order Tie Guards: v zpow
-- statement:
--   The Order Tie Guards construction uses the v zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/HeightSurvey/NotOverAndTriv.lean#L43-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/HeightSurvey/NotOverAndTriv.lean#L43-L54

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompOrd
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegQFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_HeightSurvey_NotOverAndTriv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Height GlobalTheory.Height.OrderTieGuards
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 Formalism.L2.Pj
variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  {v : AddValuation Ω (WithTop ℤ)} {la : HeightOneSpectrum (𝓞 K)}

theorem GlobalTheory.Height.OrderTieGuards.v_zpow (hv : IsNormDiscrete v) {x : Ω} (hx : x ≠ 0) {m : ℤ} (hm : v x = m) (k : ℤ) :
    v (x ^ k) = ((k * m : ℤ) : WithTop ℤ) := by sorry
