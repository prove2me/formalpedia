-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_coeff_kernelVariableChangeDeg_mem_range_of_variableChange_cuspData_xP_mem_range_gamma0Pow_level_fst
-- name    : ModularCurve.FullLevel.coeff_kernelVariableChangeDeg_mem_range_of_variableChange_cuspData_xP_mem_range_gamma0Pow_level_fst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/6ddfe70f-15e7-5e5c-aad0-f47846c3de83
-- title:
--   Coefficients of the transported μ_{p^k}-kernel lie in the level field
-- statement:
--   Fix $M'\ge 1$ and a prime $\ell\ge 3$ with $\ell\nmid M'$, and let $L$ be a field of characteristic $0$ carrying a primitive $\ell$-th root of unity $\zeta$ which is assumed to admit a ring homomorphism $\iota:L\to\mathbb C$ with $\iota\zeta=e^{2\pi i/\ell}$. Let $K$ be the intermediate field of $L\subset L((\mathsf q))$ obtained as [`ModularCurve.laurentBaseChange`](def/ModularCurve_LaurentCoeff.html#L103) of [`ModularCurve.xHFunctionField`](def/ModularCurve_XH.html#L79) at level $\ell^2M'$ for the subgroup [`ModularCurve.FullLevel.levelH`](def/ModularCurve_FullLevelJacobian.html#L22) $\ell\,M'$, i.e. the kernel of the reduction $(\mathbb Z/\ell^2M')^\times\to(\mathbb Z/\ell)^\times$; thus $K$ is generated over $L$ by the coefficientwise images of the corresponding field of $\mathbb Q$-rational $\mathsf q$-expansions. Let $p$ be a prime and $p^k\mid M'$, and let $h\in L((\mathsf q))[X]$ be a polynomial such that for every field $F'$, every ring homomorphism $f:L\to F'$ and every primitive $p^k$-th root of unity $\zeta'\in F'$, the coefficientwise image of $h$ under $f$ equals $\prod_{1\le a\le p^k/2,\;p\nmid a}\bigl(X-(\mathrm{toricPoint}\,F'\,\ell\,\zeta'^a)_1\bigr)$, the first coordinate of [`ModularCurve.toricPoint`](def/ModularCurve_TateSlots.html#L125) being the explicit series of that definition. Let $C=(u,r,s,t)$ be a Weierstrass variable change over $L((\mathsf q))$ with $r$ the constant series $-1/12$, and assume the transported abscissa $u^{-2}(x_P-r)$ of the cusp datum [`ModularCurve.cuspData`](def/ModularCurve_KatzLevelPCusps.html#L71) $L$ $\ell$ $\zeta$ at $v=(1,0)$, $w=(2,0)$ lies in $K$ (only the $P$-anchor $\mathrm{tateToricPoint}\,L\,\ell\,\zeta$ enters). Then for every $i$ the $i$-th coefficient of $u^{-2d}\,h(u^2X+r)$, with $d=$ [`ModularCurve.gamma0PowDeg`](def/ModularCurve_WeierstrassGamma0Pow.html#L53) $p$ $k$ (equal to $1$ if $p^k=2$ and to $\varphi(p^k)/2$ otherwise), lies in $K$.
--
--   This is the rationality statement for the generator kernel of $\mu_{p^k}$ on the normalised Tate curve with parameter $\mathsf q^{\ell}$: once a single transported toric abscissa is known to be a function on the modular curve of level $\ell^2M'$ with the $\wp$-normalising translation $r=-1/12$, the whole transported kernel polynomial has coefficients in that function field. It is used in the construction of the variable change producing the étale Tate datum at level $\ell$ in [`ModularCurve.FullLevel.exists_variableChange_raw_etale_tate_weightOne_level_fst_gamma0Pow`](thm.html#ModularCurve.FullLevel.exists_variableChange_raw_etale_tate_weightOne_level_fst_gamma0Pow), and rests on the comparison of $\mathsf q$-expansions of modular forms for $\Gamma_H(\ell^2M')$ with values of the toric abscissae.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_coeff_kernelVariableChangeDeg_mem_range_of_variableChange_cuspData_xP_mem_range_gamma0Pow_level_fst.lean

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

theorem ModularCurve.FullLevel.coeff_kernelVariableChangeDeg_mem_range_of_variableChange_cuspData_xP_mem_range_gamma0Pow_level_fst
    (M' : ℕ) [NeZero M']
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ ℓ)
    (hιζ : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / ℓ))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (ℓ ^ 2 * M')
        (ModularCurve.FullLevel.levelH ℓ M')))

    (p k : ℕ) [Fact p.Prime] (hpk : p ^ k ∣ M')
    (h : Polynomial (LaurentSeries L))
    (hh : ∀ (F' : Type) [Field F'] (f : L →+* F') (ζ : F'), IsPrimitiveRoot ζ (p ^ k) →
      h.map (ModularCurve.coeffMap f) =
        ∏ a ∈ (Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a),
          (X - C (ModularCurve.toricPoint F' ℓ (ζ ^ a)).1))
    (C : WeierstrassCurve.VariableChange (LaurentSeries L))
    (hx₁ : ((ModularCurve.cuspData L ℓ
        (hζ.isUnit (Fact.out : ℓ.Prime).ne_zero).unit
        ![1, 0] ![2, 0]).variableChange C).xP ∈ Set.range ((↑) : ↥K → LaurentSeries L))
    (hr : C.r = HahnSeries.C (-(12 : L)⁻¹)) :
    ∀ i : ℕ, (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h).coeff i ∈
      Set.range ((↑) : ↥K → LaurentSeries L) := by sorry
