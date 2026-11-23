-- Prove2me | Theorems.Thm_GlobalTheory_Published_exists_cc_eq_neg
-- name    : GlobalTheory.Published.exists_cc_eq_neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:48.315956+00:00
-- url     : https://prove2.me/theorems/a06695c4-a1f1-4486-8563-28045ddb998f
-- title:
--   Published: exists cc eq neg
-- statement:
--   The Published construction uses the exists cc eq neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/AlgebraMapNormOfBasisOneSqrt.lean#L252-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/AlgebraMapNormOfBasisOneSqrt.lean#L252-L257

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix TensorProduct ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory GlobalTheory.Published
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable (E)

theorem GlobalTheory.Published.exists_cc_eq_neg : ∃ θ : E, θ ≠ 0 ∧ cc θ = -θ := by sorry
