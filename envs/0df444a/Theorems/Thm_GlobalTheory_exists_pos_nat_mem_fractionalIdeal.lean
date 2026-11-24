-- Prove2me | Theorems.Thm_GlobalTheory_exists_pos_nat_mem_fractionalIdeal
-- name    : GlobalTheory.exists_pos_nat_mem_fractionalIdeal
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:36:42.858948+00:00
-- url     : https://prove2.me/theorems/6148bea0-a893-403c-8d1d-9892fb068718
-- title:
--   Global Theory: exists pos nat mem fractional Ideal
-- statement:
--   The Global Theory construction uses the exists pos nat mem fractional Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsPosNatMemFractionalIdeal.lean#L11-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsPosNatMemFractionalIdeal.lean#L11-L21

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsPosNatMemFractionalIdeal
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

theorem GlobalTheory.exists_pos_nat_mem_fractionalIdeal {E : Type} [Field E] [NumberField E]
    {a : FractionalIdeal (nonZeroDivisors (𝓞 E)) E} (ha : a ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ (n : E) ∈ a := by sorry
