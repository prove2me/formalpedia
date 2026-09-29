-- Prove2me | Theorems.Thm_ModularCurve_isCyclicKernel_tateBase_prod_X_sub_C_toricPoint_fst
-- name    : ModularCurve.isCyclicKernel_tateBase_prod_X_sub_C_toricPoint_fst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/9e32cd87-791d-5205-af57-522777939b8a
-- title:
--   μ_M gives a cyclic M-kernel polynomial on Tate(qⁿ)
-- statement:
--   Let $F$ be a field, let $M$ be a natural number carrying a primality instance with $M \neq 2$, let $\zeta \in F$ satisfy `IsPrimitiveRoot ζ M`, and let $n$ be a non-zero natural number. Consider the Weierstrass curve [`ModularCurve.tateBase F n`](def/ModularCurve_TateSlots.html#L46) over the Laurent series field $F((q))$, namely the Tate curve `tateLaurent F` (the universal Tate Weierstrass equation with coefficients in $F((q))$) transported along the ring homomorphism `qExpand F n`, which multiplies all Hahn-series exponents by $n$, i.e. substitutes $q \mapsto q^n$. For $c \in F$ let [`ModularCurve.toricPoint F n c`](def/ModularCurve_TateSlots.html#L125) be the pair of Laurent series given by the explicit $q$-expansions of Tate's coordinate functions at the toric parameter $u = c$ on $\mathrm{Tate}(q^n)$, the first component having constant term $c/(1-c)^2$ and $m$-th coefficient $\sum_{d \mid m,\, n \mid d} (m/d)\bigl(c^{m/d} + c^{-m/d}\bigr) - 2[n \mid m]\sigma_1(m/n)$. The assertion is that the monic polynomial $h = \prod_{k=1}^{(M-1)/2}\bigl(X - (\mathrm{toricPoint}\,F\,n\,(\zeta^k))_1\bigr)$ satisfies `IsCyclicKernel M` for `tateBase F n`: its natural degree is at most $(M-1)/2$, its coefficient in degree $(M-1)/2$ equals $1$, it divides the division polynomial `preΨ M` of the curve, and for every $a$ with $2 \leq a \leq (M-1)/2$ it divides $\sum_{i \le (M-1)/2} C(h_i)\,\Phi_a^{\,i}\,(\Psi_a^2)^{(M-1)/2-i}$, the numerator obtained by evaluating $h$ at the abscissa of the $a$-fold multiple.
--
--   This is the canonical $\Gamma_0(M)$-structure of the Tate curve at the cusp, expressed in Kohel kernel-polynomial form: the subgroup $\mu_M = \{u = \zeta^k\}$ of $\mathrm{Tate}(q^n)[M]$, which is the kernel of the degree-$M$ isogeny $\mathrm{Tate}(q^n) \to \mathrm{Tate}(q^{nM})$, is recorded by the polynomial whose roots are the abscissae of its non-zero points, one for each pair $\pm P$. It feeds the construction of the corresponding $\Gamma_1$-type point on the Tate curve used in the analysis of the modular curves at the cusps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isCyclicKernel_tateBase_prod_X_sub_C_toricPoint_fst.lean

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u
open Polynomial in

theorem ModularCurve.isCyclicKernel_tateBase_prod_X_sub_C_toricPoint_fst
    (F : Type u) [Field F] (M : ℕ) [Fact M.Prime] (hM2 : M ≠ 2) (ζ : F) (hζ : IsPrimitiveRoot ζ M)
    (n : ℕ) [NeZero n] :
    (ModularCurve.tateBase F n).IsCyclicKernel M
      (∏ k ∈ Finset.Icc 1 ((M - 1) / 2), (X - C (ModularCurve.toricPoint F n (ζ ^ k)).1)) := by sorry
