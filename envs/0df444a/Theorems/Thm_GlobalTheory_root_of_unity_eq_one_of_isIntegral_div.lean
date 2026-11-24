-- Prove2me | Theorems.Thm_GlobalTheory_root_of_unity_eq_one_of_isIntegral_div
-- name    : GlobalTheory.root_of_unity_eq_one_of_isIntegral_div
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:20:39.867453+00:00
-- url     : https://prove2.me/theorems/f21a59b0-c7af-4a71-96db-0a5c98589ead
-- title:
--   Global Theory: root of unity eq one of is Integral div
-- statement:
--   The Global Theory construction uses the root of unity eq one of is Integral div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/RootOfUnityEqOneOfConjCongruence.lean#L63-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/RootOfUnityEqOneOfConjCongruence.lean#L63-L86

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_RootOfUnityEqOneOfConjCongruence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix
open GlobalTheory

theorem GlobalTheory.root_of_unity_eq_one_of_isIntegral_div {E : Type} [Field E] [NumberField E] {M n : ℕ}
    (hM : 3 ≤ M) (hn : 0 < n) {u : E} (hu : u ^ n = 1) (h : IsIntegral ℤ ((u - 1) / M)) :
    u = 1 := by sorry
