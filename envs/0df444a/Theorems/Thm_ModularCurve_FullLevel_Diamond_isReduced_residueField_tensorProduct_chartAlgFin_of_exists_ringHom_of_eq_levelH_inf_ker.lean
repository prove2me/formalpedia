-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_isReduced_residueField_tensorProduct_chartAlgFin_of_exists_ringHom_of_eq_levelH_inf_ker
-- name    : ModularCurve.FullLevel.Diamond.isReduced_residueField_tensorProduct_chartAlgFin_of_exists_ringHom_of_eq_levelH_inf_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/4dcd4ea9-06a8-50c0-aae9-5e412d3dd8d0
-- title:
--   Reduced special fibre of the j-finite chart algebra of X_{H_1}(q²M')
-- statement:
--   Let $q$ be a prime and $M'\ge 1$ with $q\nmid M'$, and let $\ell_g$ be a prime with $\ell_g\equiv 11 \pmod{12}$ and $\ell_g\mid M'$. Let $L$ be a field of characteristic $0$, $\xi\in L$ a primitive $q\ell_g$-th root of unity, and assume there is a ring homomorphism $\iota:L\to\mathbb{C}$ with $\iota(\xi)=\exp(2\pi i/(q\ell_g))$. Let $H_1\le(\mathbb{Z}/q^2M')^\times$ be the intersection of `levelH` $q\,M'$, the kernel of reduction $(\mathbb{Z}/q^2M')^\times\to(\mathbb{Z}/q)^\times$, with the kernel of reduction $(\mathbb{Z}/q^2M')^\times\to(\mathbb{Z}/\ell_g)^\times$. Let $K$ be the intermediate field of $L\subseteq L(\!(q)\!)$ obtained by adjoining to $L$ the image, under the coefficientwise map $L(\!(q)\!)\leftarrow\mathbb{Q}(\!(q)\!)$ induced by $\mathbb{Q}\to L$, of the $q$-expansion function field `xHFunctionField` $(q^2M')\,H_1$ of $X_{H_1}(q^2M')$ over $\mathbb{Q}$. Let $A$ be a discrete valuation domain with fraction field $L$ such that $q$ lies in the maximal ideal of $A$, with $K$ an $A$-algebra compatibly with $A\to L\to K$, and let $j\in K$ be nonzero with underlying Laurent series the image of the classical $q$-expansion `jq` of the modular $j$-function. Then the base change to the residue field of $A$, $\kappa(A)\otimes_A \mathrm{chartAlgFin}(A,K,j)$, is a reduced ring, where $\mathrm{chartAlgFin}(A,K,j)$ is the $A$-subalgebra of $K$ consisting of the elements of $K$ integral over $A[j]$.
--
--   This is the reducedness of the special fibre of the finite ($j$-integral) chart of the two-chart integral model of the modular curve $X_{H_1}(q^2M')$ over a discrete valuation ring of residue characteristic $q$, in the variant where the level group carries both the $q$-part condition and a $\Gamma_1(\ell_g)$-type rigidifying condition at $\ell_g\mid M'$. It feeds the construction, at auxiliary level, of an isomorphism describing the chart algebra after base change, used in the geometric input to level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_isReduced_residueField_tensorProduct_chartAlgFin_of_exists_ringHom_of_eq_levelH_inf_ker.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

open scoped MatrixGroups TensorProduct

theorem ModularCurve.FullLevel.Diamond.isReduced_residueField_tensorProduct_chartAlgFin_of_exists_ringHom_of_eq_levelH_inf_ker
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓg))
    (hιξ : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓg)))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)] :
    IsReduced (TensorProduct A (IsLocalRing.ResidueField A)
      ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) := by sorry
