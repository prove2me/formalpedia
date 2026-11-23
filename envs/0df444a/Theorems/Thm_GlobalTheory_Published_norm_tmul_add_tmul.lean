-- Prove2me | Theorems.Thm_GlobalTheory_Published_norm_tmul_add_tmul
-- name    : GlobalTheory.Published.norm_tmul_add_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:42:44.929382+00:00
-- url     : https://prove2.me/theorems/1c9be65a-af96-431a-82a1-c779b94971a5
-- title:
--   Published: norm tmul add tmul
-- statement:
--   The Published construction uses the norm tmul add tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/AlgebraMapNormOfBasisOneSqrt.lean#L294-L307
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/AlgebraMapNormOfBasisOneSqrt.lean#L294-L307

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
variable (A : Type*) [CommRing A] [Algebra (maximalRealSubfield E) A]

theorem GlobalTheory.Published.norm_tmul_add_tmul {θ : E} (h0 : θ ≠ 0) (hθ : cc θ = -θ) {d : maximalRealSubfield E}
    (hd : (d : E) = θ * θ) (x y : A) :
    Algebra.norm A (x ⊗ₜ[maximalRealSubfield E] (1 : E) + y ⊗ₜ[maximalRealSubfield E] θ) =
      x ^ 2 - algebraMap (maximalRealSubfield E) A d * y ^ 2 := by sorry
