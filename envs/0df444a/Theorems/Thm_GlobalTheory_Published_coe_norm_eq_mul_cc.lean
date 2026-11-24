-- Prove2me | Theorems.Thm_GlobalTheory_Published_coe_norm_eq_mul_cc
-- name    : GlobalTheory.Published.coe_norm_eq_mul_cc
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:57:57.025808+00:00
-- url     : https://prove2.me/theorems/04db1d96-59c0-4d03-932a-862d5ae60d2d
-- title:
--   Published: coe norm eq mul cc
-- statement:
--   The Published construction uses the coe norm eq mul cc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/AlgebraMapNormOfBasisOneSqrt.lean#L284-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/AlgebraMapNormOfBasisOneSqrt.lean#L284-L290

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

theorem GlobalTheory.Published.coe_norm_eq_mul_cc (x : E) :
    ((Algebra.norm (maximalRealSubfield E) x : maximalRealSubfield E) : E) = x * cc x := by sorry
