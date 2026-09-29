-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_forall_coeff_mem_maximalIdeal_iff_of_isLevelAutAt_T_zpow_inv_of_exists_ringHom
-- name    : ModularCurve.FullLevel.AuxLevel.forall_coeff_mem_maximalIdeal_iff_of_isLevelAutAt_T_zpow_inv_of_exists_ringHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/5697aefe-b700-54ce-b14e-a338eb7f63f8
-- title:
--   Unipotent level automorphisms preserve coefficients in mathfrak m_A
-- statement:
--   Fix a prime $q \ge 5$ and a nonzero $M'$ with $q \nmid M'$, and a prime $\ell \ge 3$ with $\ell \ne q$ and $\ell \nmid M'$; let $L$ be a field of characteristic zero and $\xi \in L$ a primitive $q\ell$-th root of unity, and assume there exists a ring homomorphism $L \to \mathbb{C}$ sending $\xi$ to $\exp(2\pi i/(q\ell))$. Put $N_0 = (q\ell)^2 M'$ and let $H \le (\mathbb{Z}/N_0)^\times$ be [`ModularCurve.FullLevel.levelH (q * ℓ) M'`](def/ModularCurve_FullLevelJacobian.html#L22), the kernel of reduction $(\mathbb{Z}/N_0)^\times \to (\mathbb{Z}/q\ell)^\times$, i.e. the units congruent to $1$ modulo $q\ell$. Let $K \subseteq \mathrm{LaurentSeries}\,L$ be the intermediate field generated over $L$ by the coefficientwise image of the rational $q$-expansion function field of $\Gamma_H(N_0)$. Let $A$ be a discrete valuation domain with an $A$-algebra structure on $L$ making $L$ its fraction field, with $q \in \mathfrak m_A$ and $\xi$ in the image of $A$. Let $s \in \mathbb{Z}$ and let $\tau$ be an $L$-algebra automorphism of $K$ satisfying `IsLevelAutAt` at $\gamma = (T^s)^{-1}$ with $T =$ `ModularGroup.T`: for every weight $k$, every pair of modular forms $f, g$ on $\Gamma_H(N_0)$ with integral $q$-expansions given by power series $p_f, p_g$ over $\mathbb{Z}$, with the Laurent series of $p_g$ over $\mathbb{Q}$ nonzero, every $x \in K$ whose Laurent series is the coefficientwise image of $p_f/p_g$, and every ring homomorphism $\iota : L \to \mathbb{C}$ with $\iota(\xi) = \exp(2\pi i/(q\ell))$, one has $\iota_*(\tau x) \cdot q\text{-exp}_1(g\mid_k \sigma) = q\text{-exp}_1(f\mid_k \sigma)$, where $\sigma$ is the matrix $\begin{pmatrix} a & b/(q\ell) \\ (q\ell)c & d\end{pmatrix}$ attached to $\gamma = \begin{pmatrix} a&b\\c&d\end{pmatrix}$. Then for every $a \in K$, all Laurent coefficients of $a$ lie in the image of $\mathfrak m_A$ in $L$ if and only if all Laurent coefficients of $\tau a$ do.
--
--   The automorphism of the full-level function field attached to the inverse of the upper unipotent $T^s$ acts on width-one expansions by scaling the $n$-th coefficient by a power of the root of unity $\xi$, which is a unit of $A$; consequently it preserves the condition that all coefficients lie in the maximal ideal of $A$. The statement is used in the comparison of the two-chart integral model with the Drinfeld chart at auxiliary level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_forall_coeff_mem_maximalIdeal_iff_of_isLevelAutAt_T_zpow_inv_of_exists_ringHom.lean

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

theorem ModularCurve.FullLevel.AuxLevel.forall_coeff_mem_maximalIdeal_iff_of_isLevelAutAt_T_zpow_inv_of_exists_ringHom
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))

    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hξA : ∃ x : A, algebraMap A L x = ξ)
    (s : ℤ)
    (τ : ↥K ≃ₐ[L] ↥K)
    (hτ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
      (ModularCurve.FullLevel.levelH (q * ℓ) M') (ModularGroup.T ^ s)⁻¹ K τ)
    (a : ↥K) :
    (∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A, (((a : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m) ↔
    (∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A, (((τ a : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m) := by sorry
