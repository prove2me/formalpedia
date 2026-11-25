-- Prove2me | Theorems.Thm_GlobalTheory_Height_OrderTieGuards_zero_of_notMem
-- name    : GlobalTheory.Height.OrderTieGuards.zero_of_notMem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T02:43:24.171223+00:00
-- url     : https://prove2.me/theorems/f5a2bf2c-762e-4b72-a225-d2ac77886c26
-- title:
--   Order Tie Guards: zero of not Mem
-- statement:
--   The Order Tie Guards construction uses the zero of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/HeightSurvey/NotOverAndTriv.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/HeightSurvey/NotOverAndTriv.lean#L27-L29

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

theorem GlobalTheory.Height.OrderTieGuards.zero_of_notMem (ho : IsOver (K := K) v la) {a : 𝓞 K} (ha : a ∉ la.asIdeal) :
    v (algebraMap K Ω (a : K)) = 0 := by sorry
