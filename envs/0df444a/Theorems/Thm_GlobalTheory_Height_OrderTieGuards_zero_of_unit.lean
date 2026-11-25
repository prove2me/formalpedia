-- Prove2me | Theorems.Thm_GlobalTheory_Height_OrderTieGuards_zero_of_unit
-- name    : GlobalTheory.Height.OrderTieGuards.zero_of_unit
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T02:43:10.099898+00:00
-- url     : https://prove2.me/theorems/57ef4313-7284-4da9-b3eb-50ff25d08528
-- title:
--   Order Tie Guards: zero of unit
-- statement:
--   The Order Tie Guards construction uses the zero of unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/HeightSurvey/NotOverAndTriv.lean#L31-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/HeightSurvey/NotOverAndTriv.lean#L31-L41

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

theorem GlobalTheory.Height.OrderTieGuards.zero_of_unit (ho : IsOver (K := K) v la) {u : K} (hu : la.valuation K u = 1) :
    v (algebraMap K Ω u) = 0 := by sorry
