-- Prove2me | Theorems.Thm_ModularCurve_exists_isIntegralQExp_smul_atkinLehnerSlash_of_even
-- name    : ModularCurve.exists_isIntegralQExp_smul_atkinLehnerSlash_of_even
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/82d6ccdc-73b0-5e46-aa3d-dd8b55a489a1
-- title:
--   Integrality of q-expansions under the Atkin–Lehner matrix at ℓ
-- statement:
--   Let $M$ and $\ell$ be nonzero natural numbers, let $k$ be an even integer, and let $f$ be a modular form of weight $k$ for the image in $\mathrm{GL}(2,\mathbb{R})$ of the congruence subgroup $\Gamma_1(M)\cap\Gamma_0(M\ell)\le \mathrm{SL}(2,\mathbb{Z})$. Suppose $p\in\mathbb{Z}[[X]]$ is an integral $q$-expansion for $f$ in the sense of [`ModularCurve.IsIntegralQExp`](def/ModularCurve_X1.html#L37), i.e. the coefficientwise image of $p$ under $\mathbb{Z}\to\mathbb{C}$ equals the $q$-expansion of $f$ of period $1$, `qExpansion 1 f`. Let $\gamma\in\mathrm{SL}(2,\mathbb{Z})$ lie in $\Gamma_0(M)$ and assume $\ell$ divides the entry $\gamma_{1,1}$ (zero-indexed, i.e. the lower right entry $d$). The conclusion asserts the existence of a nonzero integer $D$ and a power series $p_1\in\mathbb{Z}[[X]]$ such that $p_1$ is an integral $q$-expansion, again of period $1$, for the function $$\tau\mapsto D\cdot\bigl(f\mid_k\gamma\bigr)\bigl(\mathrm{diag}(\ell,1)\cdot\tau\bigr),$$ where $\mathrm{diag}(\ell,1)$ is [`ModularForm.heckeDiagMatrix ℓ`](def/ModularForm_HeckeOperator.html#L21), the upper triangular element $!![\ell,0;0,1]$ of $\mathrm{GL}(2,\mathbb{R})$, acting on the upper half plane by $\tau\mapsto \ell\tau$. Thus some nonzero integer multiple of $\tau\mapsto (f\mid_k\gamma)(\ell\tau)$ has integral Fourier coefficients at $\infty$.
--
--   The matrices $\gamma\,\mathrm{diag}(\ell,1)$ with $\gamma\in\Gamma_0(M)$ and $\ell\mid d$ are the Atkin–Lehner matrices at $\ell$ for the level $\Gamma_1(M)\cap\Gamma_0(M\ell)$, so the statement says that the Atkin–Lehner involution at $\ell$ preserves integrality of the $q$-expansion at $\infty$ up to a bounded denominator $D$. It feeds the integrality statements for Atkin–Lehner slashes of cusp forms and the identifications of the function field of the modular curve with its Atkin–Lehner and Hecke twists used further on.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_isIntegralQExp_smul_atkinLehnerSlash_of_even.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups ModularForm in

theorem ModularCurve.exists_isIntegralQExp_smul_atkinLehnerSlash_of_even (M ℓ : ℕ) [NeZero M]
    [NeZero ℓ] {k : ℤ} (hk : Even k)
    (f : ModularForm ((CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 (M * ℓ) :
      Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
    {p : PowerSeries ℤ} (hp : ModularCurve.IsIntegralQExp f p)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (hγℓ : (ℓ : ℤ) ∣ γ 1 1) :
    ∃ (D : ℤ) (p₁ : PowerSeries ℤ), D ≠ 0 ∧
      ModularCurve.IsIntegralQExp
        ((D : ℂ) • fun τ : UpperHalfPlane =>
          ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ) (ModularForm.heckeDiagMatrix ℓ • τ)) p₁ := by sorry
