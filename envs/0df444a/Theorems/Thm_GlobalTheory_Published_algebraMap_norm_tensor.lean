-- Prove2me | Theorems.Thm_GlobalTheory_Published_algebraMap_norm_tensor
-- name    : GlobalTheory.Published.algebraMap_norm_tensor
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:30.935791+00:00
-- url     : https://prove2.me/theorems/234c58ef-dc12-46f6-9384-f102e0ee9fa9
-- title:
--   Published: algebra Map norm tensor
-- statement:
--   The Published construction uses the algebra Map norm tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/AlgebraMapNormOfBasisOneSqrt.lean#L309-L322
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/AlgebraMapNormOfBasisOneSqrt.lean#L309-L322

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

theorem GlobalTheory.Published.algebraMap_norm_tensor (z : A ⊗[maximalRealSubfield E] E) :
    algebraMap A (A ⊗[maximalRealSubfield E] E) (Algebra.norm A z) =
      z * Algebra.TensorProduct.map (AlgHom.id A A) (IsCMField.complexConj E).toAlgHom z := by sorry
