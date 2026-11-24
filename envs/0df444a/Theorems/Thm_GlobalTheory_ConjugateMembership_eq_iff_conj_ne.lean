-- Prove2me | Theorems.Thm_GlobalTheory_ConjugateMembership_eq_iff_conj_ne
-- name    : GlobalTheory.ConjugateMembership.eq_iff_conj_ne
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:25:42.715468+00:00
-- url     : https://prove2.me/theorems/0a526503-be2d-4d92-a6ef-87d6fa1b51e9
-- title:
--   Conjugate Membership: eq iff conj ne
-- statement:
--   The Conjugate Membership construction uses the eq iff conj ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/EqIffConjNe.lean#L26-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/EqIffConjNe.lean#L26-L39

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

theorem GlobalTheory.ConjugateMembership.eq_iff_conj_ne {x r : ℂ} {d : ℝ} (hd : 0 < d) (hx : x ^ 2 = -(d : ℂ)) (hr : r ^ 2 = -(d : ℂ)) :
    x = r ↔ ¬ (starRingEnd ℂ) x = r := by sorry
