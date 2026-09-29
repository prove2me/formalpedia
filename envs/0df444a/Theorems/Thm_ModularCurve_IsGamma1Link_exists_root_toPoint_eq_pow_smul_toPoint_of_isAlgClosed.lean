-- Prove2me | Theorems.Thm_ModularCurve_IsGamma1Link_exists_root_toPoint_eq_pow_smul_toPoint_of_isAlgClosed
-- name    : ModularCurve.IsGamma1Link.exists_root_toPoint_eq_pow_smul_toPoint_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/3031f061-56f6-5b97-8720-bc88ae81cfed
-- title:
--   Linked Γ₁(ℓ)-point is ℓ^{k-1} times a kernel root
-- statement:
--   Let $\kappa$ be an algebraically closed field with decidable equality, let $\ell$ be prime with $3 \le \ell$ and $\ell \neq 0$ in $\kappa$, and let $M'$ be a natural number having $\ell$ among its prime factors; write $k = v_\ell(M')$ for the exponent of $\ell$ in the factorisation of $M'$. Let $W$ be a Weierstrass curve over $\kappa$ whose discriminant $\Delta$ is a unit, and let $h$ assign to each prime factor $p$ of $M'$ a polynomial $h_p \in \kappa[X]$ satisfying [`ModularCurve.IsGamma0PowAt`](def/ModularCurve_WeierstrassGamma0Pow.html#L55) for $p$ and the exponent $v_p(M')$: that is, when $p^{v_p(M')} = 2$, the conditions $\deg h_p \le 1$, $\mathrm{coeff}_1(h_p) = 1$ and $h_p \mid \Psi_2^{\mathrm{Sq}}$; otherwise, with $n = \varphi(p^{v_p(M')})/2$, the conditions $\deg h_p \le n$, $\mathrm{coeff}_n(h_p) = 1$, $h_p \cdot \mathrm{pre}\Psi_{p^{v_p(M')-1}} \mid \mathrm{pre}\Psi_{p^{v_p(M')}}$, and $h_p \mid W.\mathrm{smulNumerator}\,a\,n\,h_p$ for all $a$ with $2 \le a \le (p^{v_p(M')}-1)/2$ and $p \nmid a$. Let $D$ be a quadruple $(x_P, y_P, x_Q, y_Q)$ of elements of $\kappa$ which is a $\Gamma_1(\ell)$-point of $W$, i.e. $(x_P,y_P)$ satisfies the affine Weierstrass equation, $(\mathrm{pre}\Psi_\ell)(x_P) = 0$, and $x_Q = x_P$, $y_Q = y_P$; and assume the link condition that $h_\ell$ divides $\prod_{a=1}^{(\ell-1)/2}\bigl(\Phi_{\ell^{k-1}}\cdot \Psi^{\mathrm{Sq}}_a(x_P) - \Phi_a(x_P)\cdot \Psi^{\mathrm{Sq}}_{\ell^{k-1}}\bigr)$ in $\kappa[X]$. Then there are $x_G, y_G \in \kappa$ satisfying the affine Weierstrass equation of $W$, with $h_\ell(x_G) = 0$, such that the point of the base change of $W$ to $\kappa$ attached to $(x_P,y_P)$ equals $\ell^{k-1}$ times the point attached to $(x_G,y_G)$, where in each case the attached point is the affine point with those coordinates if they are nonsingular and $0$ otherwise.
--
--   This is the $\Gamma_0$-compatibility clause for level structures of type $\Gamma_0(M') \cap \Gamma_1(\ell)$: read over an algebraically closed field, the divisibility link between the generator-kernel polynomials of the $\Gamma_0(M')$-structure and the $\Gamma_1(\ell)$-point says that the $\Gamma_1(\ell)$-point is $\ell^{k-1}$ times a generator of the $\ell$-primary part of the $\Gamma_0$-subgroup. It feeds the count [`ModularCurve.natCard_levelPData_isGamma1Point_and_isGamma1Link_eq_of_isAlgClosed`](thm.html#ModularCurve.natCard_levelPData_isGamma1Point_and_isGamma1Link_eq_of_isAlgClosed) and the existence statements for the supersingular-fibre dictionary of the $\Gamma_1$-power rigid datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IsGamma1Link_exists_root_toPoint_eq_pow_smul_toPoint_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import Definitions.Def_ModularCurve_LevelRelabelling

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.IsGamma1Link.exists_root_toPoint_eq_pow_smul_toPoint_of_isAlgClosed
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (ℓ M' : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓκ : (ℓ : κ) ≠ 0) (hmem : ℓ ∈ M'.primeFactors)
    (W : WeierstrassCurve κ) (hΔ : IsUnit W.Δ)
    (h : ↥M'.primeFactors → Polynomial κ) (hh : ∀ p : ↥M'.primeFactors, ModularCurve.IsGamma0PowAt W (p : ℕ) (M'.factorization (p : ℕ)) (h p))
    (D : ModularCurve.LevelPData κ) (hD : ModularCurve.IsGamma1Point W ℓ D)
    (hlink : ModularCurve.IsGamma1Link W ℓ M' h D) :
    ∃ (xG yG : κ),
      W.toAffine.Equation xG yG ∧ (h ⟨ℓ, hmem⟩).eval xG = 0 ∧
      ModularCurve.LevelRelabelling.toPoint (W.baseChange κ) D.xP D.yP =
        (ℓ ^ (M'.factorization ℓ - 1)) • ModularCurve.LevelRelabelling.toPoint (W.baseChange κ) xG yG := by sorry
