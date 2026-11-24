-- Prove2me | Theorems.Thm_GlobalTheory_ConjugateMembership_conj_eq_neg_of_sq
-- name    : GlobalTheory.ConjugateMembership.conj_eq_neg_of_sq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:25:43.804103+00:00
-- url     : https://prove2.me/theorems/3ff03f8a-e770-475f-a3f2-ab7bacba15aa
-- title:
--   Conjugate Membership: conj eq neg of sq
-- statement:
--   The Conjugate Membership construction uses the conj eq neg of sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/EqIffConjNe.lean#L9-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/EqIffConjNe.lean#L9-L24

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqIffConjNe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ConjugateMembership
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.ConjugateMembership.conj_eq_neg_of_sq {x : ℂ} {d : ℝ} (hd : 0 < d) (hx : x ^ 2 = -(d : ℂ)) :
    (starRingEnd ℂ) x = -x := by sorry
