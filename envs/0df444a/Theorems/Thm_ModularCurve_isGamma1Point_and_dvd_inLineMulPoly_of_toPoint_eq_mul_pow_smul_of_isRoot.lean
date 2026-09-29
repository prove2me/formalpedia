-- Prove2me | Theorems.Thm_ModularCurve_isGamma1Point_and_dvd_inLineMulPoly_of_toPoint_eq_mul_pow_smul_of_isRoot
-- name    : ModularCurve.isGamma1Point_and_dvd_inLineMulPoly_of_toPoint_eq_mul_pow_smul_of_isRoot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/ecf54568-c189-5011-bbc2-a4291b9b7355
-- title:
--   Multiples bℓ^{k-1}G are linked Γ₁(ℓ)-points
-- statement:
--   Let $\kappa$ be an algebraically closed field with decidable equality, let $\ell$ be prime with $3\le\ell$ and $\ell\neq 0$ in $\kappa$, and let $M'$ be a natural number having $\ell$ among its prime factors; put $k=v_p(M')$ for each prime factor $p$. Let $W$ be a Weierstrass curve over $\kappa$ whose discriminant $W.\Delta$ is a unit, and let $h$ assign to each prime factor $p$ of $M'$ a polynomial $h_p\in\kappa[X]$ satisfying `IsGamma0PowAt` at $(p,v_p(M'))$: if $p^{v_p(M')}=2$ then $h_p$ has degree at most $1$, coefficient $1$ in degree $1$ and divides $W.\Psi_2^{\mathrm{Sq}}$; otherwise $\deg h_p\le\varphi(p^{v_p(M')})/2$, the coefficient of $h_p$ in that degree is $1$, $h_p\cdot W.\mathrm{pre}\Psi(p^{v_p(M')-1})$ divides $W.\mathrm{pre}\Psi(p^{v_p(M')})$, and $h_p$ divides $W.\mathrm{smulNumerator}\,a\,(\varphi(p^{v_p(M')})/2)\,h_p$ for every $a$ with $2\le a\le(p^{v_p(M')}-1)/2$ and $p\nmid a$. Assume $(x_G,y_G)$ satisfies the affine equation of $W$ and $h_\ell(x_G)=0$; let $b$ be a natural number with $\ell\nmid b$; and let $D=(x_P,y_P,x_Q,y_Q)$ be a `LevelPData` over $\kappa$ with $(x_P,y_P)$ on the curve, $x_Q=x_P$, $y_Q=y_P$, and, writing $\mathrm{toPoint}$ for the affine point $\mathrm{some}\,x\,y$ when $(x,y)$ is nonsingular and $0$ otherwise, $\mathrm{toPoint}(x_P,y_P)=(b\,\ell^{v_\ell(M')-1})\cdot\mathrm{toPoint}(x_G,y_G)$ on $W$ base changed to $\kappa$. Then $D$ is a $\Gamma_1(\ell)$-point of $W$, i.e. $(x_P,y_P)$ satisfies the equation, $(W.\mathrm{pre}\Psi\,\ell)(x_P)=0$, $x_Q=x_P$ and $y_Q=y_P$; and $h_\ell$ divides $$\prod_{a=1}^{(\ell-1)/2}\Bigl(W.\Phi_n\cdot C\bigl((W.\Psi^{\mathrm{Sq}}_a)(x_P)\bigr)-C\bigl((W.\Phi_a)(x_P)\bigr)\cdot W.\Psi^{\mathrm{Sq}}_n\Bigr),\qquad n=\ell^{v_\ell(M')-1}.$$
--
--   This is the converse half of the identification of the linked $\Gamma_1(\ell)$-points with the nonzero $\ell$-torsion of the cyclic subgroup cut out by the $\ell$-component of a $\Gamma_0(M')$-tuple: every multiple $b\ell^{v_\ell(M')-1}G$ of a generator $G$, read as a coincident pair, is such a point and satisfies the divisibility expressing the link. It feeds the count of linked $\Gamma_1(\ell)$-points over an algebraically closed field, [`ModularCurve.natCard_levelPData_isGamma1Point_and_isGamma1Link_eq_of_isAlgClosed`](thm.html#ModularCurve.natCard_levelPData_isGamma1Point_and_isGamma1Link_eq_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isGamma1Point_and_dvd_inLineMulPoly_of_toPoint_eq_mul_pow_smul_of_isRoot.lean

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import Definitions.Def_ModularCurve_LevelRelabelling

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.isGamma1Point_and_dvd_inLineMulPoly_of_toPoint_eq_mul_pow_smul_of_isRoot
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (ℓ M' : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓκ : (ℓ : κ) ≠ 0) (hmem : ℓ ∈ M'.primeFactors)
    (W : WeierstrassCurve κ) (hΔ : IsUnit W.Δ)
    (h : ↥M'.primeFactors → Polynomial κ) (hh : ∀ p : ↥M'.primeFactors, ModularCurve.IsGamma0PowAt W (p : ℕ) (M'.factorization (p : ℕ)) (h p))
    (xG yG : κ) (hG : W.toAffine.Equation xG yG) (hroot : (h ⟨ℓ, hmem⟩).eval xG = 0)
    (b : ℕ) (hb : ¬ ℓ ∣ b)
    (D : ModularCurve.LevelPData κ) (hDP : W.toAffine.Equation D.xP D.yP)
    (hDQ : D.xQ = D.xP ∧ D.yQ = D.yP)
    (hPG : ModularCurve.LevelRelabelling.toPoint (W.baseChange κ) D.xP D.yP =
      (b * ℓ ^ (M'.factorization ℓ - 1)) • ModularCurve.LevelRelabelling.toPoint (W.baseChange κ) xG yG) :
    ModularCurve.IsGamma1Point W ℓ D ∧
      h ⟨ℓ, hmem⟩ ∣ ModularCurve.inLineMulPoly W ℓ (ℓ ^ (M'.factorization ℓ - 1)) D.xP := by sorry
