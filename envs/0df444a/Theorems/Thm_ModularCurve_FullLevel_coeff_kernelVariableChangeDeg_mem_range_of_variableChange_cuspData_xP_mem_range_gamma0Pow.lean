-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_coeff_kernelVariableChangeDeg_mem_range_of_variableChange_cuspData_xP_mem_range_gamma0Pow
-- name    : ModularCurve.FullLevel.coeff_kernelVariableChangeDeg_mem_range_of_variableChange_cuspData_xP_mem_range_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/bb0a2699-cb6b-5682-81bc-23544b5df983
-- title:
--   Transported μ_{p^k} kernel has coefficients in the level field
-- statement:
--   Let $q\ge 5$ and $\ell\ge 3$ be primes with $\ell\ne q$, let $M'\ge 1$ be a natural number divisible by neither $q$ nor $\ell$, let $L$ be a field of characteristic zero and $\xi\in L$ a primitive $(q\ell)$-th root of unity, assumed to admit a ring homomorphism $\iota\colon L\to\mathbb{C}$ with $\iota(\xi)=\exp(2\pi i/(q\ell))$. Let $K$ be the intermediate field of $L\subseteq L((\mathsf q))$ obtained by adjoining to $L$ the coefficientwise image of the modular function field [`ModularCurve.xHFunctionField ((q*ℓ)^2*M') (ModularCurve.FullLevel.levelH (q*ℓ) M')`](def/ModularCurve_XH.html#L79), where `levelH` is the kernel of the reduction $(\mathbb{Z}/(q\ell)^2M')^\times\to(\mathbb{Z}/q\ell)^\times$. Let $p$ be a prime and $k$ with $p^k\mid M'$, and let $h\in L((\mathsf q))[X]$ be such that for every field $F'$, every ring homomorphism $f\colon L\to F'$ and every primitive $p^k$-th root of unity $\zeta\in F'$, the coefficientwise image of $h$ equals $\prod_{1\le a\le p^k/2,\ p\nmid a}\bigl(X-(\mathrm{toricPoint}\,F'\,(q\ell)\,\zeta^{a})_1\bigr)$, the first coordinates being the explicit Tate-curve abscissa series. Let $C=(u,r,s,t)$ be a Weierstrass variable change over $L((\mathsf q))$ such that $u^{-2}\bigl(x_\xi-r\bigr)$ and $u^{-2}\bigl(x_{\xi^2}-r\bigr)$ lie in $K$, where $x_{\xi^{j}}$ denotes the `xP`-coordinate of [`ModularCurve.cuspData L (q*ℓ)`](def/ModularCurve_KatzLevelPCusps.html#L71) at the vectors $\binom{1}{0},\binom{2}{0}$ and $\binom{2}{0},\binom{1}{0}$ respectively. Then every coefficient of $u^{-2d}\,h\bigl(u^2X+r\bigr)$, with $d=$ [`ModularCurve.gamma0PowDeg p k`](def/ModularCurve_WeierstrassGamma0Pow.html#L53) ($=1$ if $p^k=2$, and $\varphi(p^k)/2$ otherwise), lies in $K$.
--
--   This is the statement that transporting the kernel polynomial of $\mu_{p^k}$ on the Tate curve along a variable change that carries the two distinguished cusp abscissae into the level field keeps all coefficients in that field. It is used in the construction of points of the $\Gamma_0(p^k)$-type level moduli problem over the base-changed function field of $X_H$ of level $(q\ell)^2M'$, and in the corresponding existence statement for a variable change on the rigidified Tate data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_coeff_kernelVariableChangeDeg_mem_range_of_variableChange_cuspData_xP_mem_range_gamma0Pow.lean

import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Sqf
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

theorem ModularCurve.FullLevel.coeff_kernelVariableChangeDeg_mem_range_of_variableChange_cuspData_xP_mem_range_gamma0Pow
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hιξ : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))

    (p k : ℕ) [Fact p.Prime] (hpk : p ^ k ∣ M')
    (h : Polynomial (LaurentSeries L))
    (hh : ∀ (F' : Type) [Field F'] (f : L →+* F') (ζ : F'), IsPrimitiveRoot ζ (p ^ k) →
      h.map (ModularCurve.coeffMap f) =
        ∏ a ∈ (Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a),
          (X - C (ModularCurve.toricPoint F' (q * ℓ) (ζ ^ a)).1))
    (C : WeierstrassCurve.VariableChange (LaurentSeries L))
    (hx₁ : ((ModularCurve.cuspData L (q * ℓ)
        (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit
        ![1, 0] ![2, 0]).variableChange C).xP ∈ Set.range ((↑) : ↥K → LaurentSeries L))
    (hx₂ : ((ModularCurve.cuspData L (q * ℓ)
        (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit
        ![2, 0] ![1, 0]).variableChange C).xP ∈ Set.range ((↑) : ↥K → LaurentSeries L)) :
    ∀ i : ℕ, (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h).coeff i ∈
      Set.range ((↑) : ↥K → LaurentSeries L) := by sorry
