-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_forall_coeff_mem_maximalIdeal_iff_of_isLevelAutAt_T_zpow_inv_of_exists_ringHom_of_isPrimitiveRoot_mul_of_dvd
-- name    : ModularCurve.FullLevel.AuxLevelOne.forall_coeff_mem_maximalIdeal_iff_of_isLevelAutAt_T_zpow_inv_of_exists_ringHom_of_isPrimitiveRoot_mul_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/9d28421d-3c07-5b2d-822e-182fb6bed5df
-- title:
--   Unipotent level automorphisms preserve mathfrak m_A-integral q-expansion coefficients
-- statement:
--   Fix a prime $q$, a nonzero natural number $M'$ with $q \nmid M'$, and a prime $\ell$ with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Let $L$ be a field of characteristic zero containing a primitive $q$-th root of unity $\zeta$ and a primitive $q\ell$-th root of unity $\xi$, such that some ring homomorphism $\iota_0 : L \to \mathbb C$ sends $\xi$ to $e^{2\pi i/(q\ell)}$, and with $\zeta = \xi^{\ell}$. Let $H_1 \le (\mathbb Z/q^2M')^\times$ be the intersection of [`ModularCurve.FullLevel.levelH q M'`](def/ModularCurve_FullLevelJacobian.html#L22) (the kernel of the unit-group reduction map out of $(\mathbb Z/q^2M')^\times$ attached to the divisibility `dvd_sq_mul q M'`) with the kernel of reduction $(\mathbb Z/q^2M')^\times \to (\mathbb Z/\ell)^\times$, and let $K$ be the intermediate field of $L((X))$ generated over $L$ by the coefficientwise image of the field of $q$-expansions of modular functions for $\Gamma_{H_1}(q^2M') \le \mathrm{SL}_2(\mathbb Z)$, i.e. `laurentBaseChange L (xHFunctionField (q ^ 2 * M') H₁)`. Let $A$ be a discrete valuation domain with fraction field $L$ such that $q \in \mathfrak m_A$ and $\xi$ lies in the image of $A$. Let $s \in \mathbb Z$ and let $\tau$ be an $L$-algebra automorphism of $K$ which `IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ (ModularGroup.T ^ s)⁻¹ K τ`: for every weight $k$, every pair of modular forms $f,g$ of weight $k$ for $\Gamma_{H_1}(q^2M')$ with integral $q$-expansions $p_f, p_g$ and $p_g \neq 0$, every $x \in K$ whose Laurent series is the image of $p_f/p_g$, and every ring homomorphism $\iota : L \to \mathbb C$ with $\iota(\zeta) = e^{2\pi i/q}$, one has $\iota(\tau x) \cdot (g \mid_k \mathrm{conjElemN}\,q\,(T^s)^{-1})^{\wedge} = (f \mid_k \mathrm{conjElemN}\,q\,(T^s)^{-1})^{\wedge}$ as Laurent series over $\mathbb C$, where $\mathrm{conjElemN}\,m\,\gamma$ is the matrix $\begin{pmatrix} a & b/m \\ mc & d\end{pmatrix} \in \mathrm{GL}_2(\mathbb R)$ for $\gamma = \begin{pmatrix} a& b\\ c&d\end{pmatrix}$. Then for every $a \in K$: all Laurent coefficients $\mathrm{coeff}_n(a)$, $n \in \mathbb Z$, lie in the image of $\mathfrak m_A$ under $A \to L$ if and only if the same holds for all coefficients of $\tau a$.
--
--   This is the invariance, under the level automorphism attached to the upper unipotent matrix $(T^s)^{-1}$, of the condition that a $q$-expansion in the function field of $X_{H_1}(q^2M')$ over $L$ have all coefficients in the maximal ideal of the chosen valuation ring $A$; it is the auxiliary-level variant in which the full level $\Gamma(q\ell)$ is replaced by a level with trivial diamond at the guard prime $\ell$, so that no lower bound on $q$ is required. It feeds the comparison of the two integral charts on the model of the curve in [`ModularCurve.FullLevel.AuxLevelOne.forall_mem_comap_drinfeldChart_iff_forall_coeff_mem_maximalIdeal_of_linearPart_riders_twoChartIntegralModel_of_isPrimitiveRoot_mul_of_dvd`](thm.html#ModularCurve.FullLevel.AuxLevelOne.forall_mem_comap_drinfeldChart_iff_forall_coeff_mem_maximalIdeal_of_linearPart_riders_twoChartIntegralModel_of_isPrimitiveRoot_mul_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevelOne_forall_coeff_mem_maximalIdeal_iff_of_isLevelAutAt_T_zpow_inv_of_exists_ringHom_of_isPrimitiveRoot_mul_of_dvd.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

open scoped MatrixGroups

theorem ModularCurve.FullLevel.AuxLevelOne.forall_coeff_mem_maximalIdeal_iff_of_isLevelAutAt_T_zpow_inv_of_exists_ringHom_of_isPrimitiveRoot_mul_of_dvd
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))

    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (hζξ : ζ = ξ ^ ℓ)
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hξA : ∃ x : A, algebraMap A L x = ξ)
    (s : ℤ)
    (τ : ↥K ≃ₐ[L] ↥K)
    (hτ : ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ (ModularGroup.T ^ s)⁻¹ K τ)
    (a : ↥K) :
    (∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A, (((a : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m) ↔
    (∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A, (((τ a : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m) := by sorry
