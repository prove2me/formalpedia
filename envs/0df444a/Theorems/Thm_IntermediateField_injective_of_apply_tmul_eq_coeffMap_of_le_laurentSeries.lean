-- Prove2me | Theorems.Thm_IntermediateField_injective_of_apply_tmul_eq_coeffMap_of_le_laurentSeries
-- name    : IntermediateField.injective_of_apply_tmul_eq_coeffMap_of_le_laurentSeries
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/85025e08-046b-53b1-933f-ae693d88afab
-- title:
--   Linear disjointness of k and κ((q)) over κ
-- statement:
--   Let $\kappa$ and $k$ be fields with $k$ a $\kappa$-algebra, and let $R$ be an intermediate field of the extension $\kappa(\!(q)\!)/\kappa$, where $\kappa(\!(q)\!)$ denotes the field `LaurentSeries κ` of formal Laurent series over $\kappa$. Let $\varphi : k \otimes_{\kappa} R \to k(\!(q)\!)$ be a homomorphism of $k$-algebras, and assume that for every $r \in R$ one has $\varphi(1 \otimes_{\kappa} r) =$ the image of $r$, regarded as an element of $\kappa(\!(q)\!)$, under [`ModularCurve.coeffMap (algebraMap κ k)`](def/ModularCurve_LaurentCoeff.html#L16); here `coeffMap f` is the ring homomorphism $\mathrm{LaurentSeries}\,R \to \mathrm{LaurentSeries}\,S$ attached to a ring homomorphism $f : R \to S$ which applies $f$ to each coefficient, so that the hypothesis says $\varphi(1 \otimes \sum_n a_n q^n) = \sum_n f(a_n) q^n$ with $f$ the structure map $\kappa \to k$. The conclusion is that $\varphi$ is injective. No hypothesis of algebraicity, separability or finiteness on $k/\kappa$ or on $R$ is imposed, and the characteristic is arbitrary.
--
--   This is the statement that $k$ and $\kappa(\!(q)\!)$ are linearly disjoint over $\kappa$ inside $k(\!(q)\!)$, in the form of injectivity of a $k$-algebra map out of $k \otimes_\kappa R$ that acts coefficientwise on $R$; in particular $k \otimes_\kappa R$ has no nonzero nilpotents or zero divisors. It is used in the construction of integral models of modular curves by base change of chart algebras, being cited by [`AlgebraicCurve.TwoChartIntegralModel.exists_algEquiv_tensorProduct_chartAlg_adjoin_coeffMap_of_isIntegrallyClosed`](thm.html#AlgebraicCurve.TwoChartIntegralModel.exists_algEquiv_tensorProduct_chartAlg_adjoin_coeffMap_of_isIntegrallyClosed) and by the two results on maximal ideals of chart algebras at full level whose $q$-expansions involve cyclotomic coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IntermediateField_injective_of_apply_tmul_eq_coeffMap_of_le_laurentSeries.lean

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem IntermediateField.injective_of_apply_tmul_eq_coeffMap_of_le_laurentSeries
    (κ : Type u) [Field κ] (k : Type v) [Field k] [Algebra κ k]
    (R : IntermediateField κ (LaurentSeries κ))
    (φ : k ⊗[κ] ↥R →ₐ[k] LaurentSeries k)
    (hφ : ∀ r : ↥R, φ (1 ⊗ₜ[κ] r) = ModularCurve.coeffMap (algebraMap κ k) ((r : ↥R) : LaurentSeries κ)) :
    Function.Injective φ := by sorry
