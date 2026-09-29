-- Prove2me | Theorems.Thm_ModularCurve_exists_isGamma0PowAt_tateBase_and_map_coeffMap_eq_prod_X_sub_C_toricPoint
-- name    : ModularCurve.exists_isGamma0PowAt_tateBase_and_map_coeffMap_eq_prod_X_sub_C_toricPoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/aff1818b-464c-5f3c-b0a3-d571db17c7e9
-- title:
--   A rational Γ₀(p^k)-structure on the Tate curve
-- statement:
--   Let $F$ be a field, $p$ a prime, $k$ a natural number, and suppose $p \neq 0$ in $F$; let $n \geq 1$. Then there is a polynomial $h$ over the Laurent series ring $\mathrm{LaurentSeries}\,F$ with the following two properties. First, [`ModularCurve.IsGamma0PowAt`](def/ModularCurve_WeierstrassGamma0Pow.html#L55) holds for the Weierstrass curve [`ModularCurve.tateBase F n`](def/ModularCurve_TateSlots.html#L46) — the Tate curve over $\mathrm{LaurentSeries}\,F$ with the uniformiser raised to the $n$-th power, i.e. the image of `tateLaurent F` under the exponent-scaling ring homomorphism `qExpand` — with data $p,k,h$: that is, if $p^k = 2$ then $h$ has degree at most $1$, coefficient $1$ in degree $1$, and divides the quantity $\Psi_2^{\,2}$ of that curve; while if $p^k \neq 2$ then $h$ has degree at most $\varphi(p^k)/2$, coefficient $1$ in degree $\varphi(p^k)/2$, the product $h \cdot \mathrm{pre}\Psi_{p^{k-1}}$ divides $\mathrm{pre}\Psi_{p^k}$, and $h$ divides $\mathrm{smulNumerator}\,a\,(\varphi(p^k)/2)\,h$ for every $a$ with $2 \le a \le (p^k-1)/2$ and $p \nmid a$. Secondly, the single polynomial $h$ is universal for the expected factorisation: for every field $F'$, every ring homomorphism $f : F \to F'$ and every primitive $p^k$-th root of unity $\zeta \in F'$, the image of $h$ under coefficientwise application of $f$ to Laurent series equals $\prod_{1 \le a \le p^k/2,\ p \nmid a} \bigl(X - (\mathrm{toricPoint}\,F'\,n\,(\zeta^a))_1\bigr)$, where $\mathrm{toricPoint}\,F'\,n\,c$ is the explicit pair of Laurent series, given by divisor-sum coefficient formulae, attached to the parameter $c$, and the subscript denotes its first coordinate.
--
--   This provides the $\Gamma_0(p^k)$-level structure at a cusp: the kernel polynomial cutting out the generators of the $\mu_{p^k}$ part of the Tate curve, which a priori is defined only after adjoining a primitive $p^k$-th root of unity, is in fact defined over the ground field, and base changes to the expected product of linear factors in the toric points $\zeta^a$. It is used in the analysis of the Tate-curve points of the moduli problems with full level and $\Gamma_0(p^k)$-level structure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_isGamma0PowAt_tateBase_and_map_coeffMap_eq_prod_X_sub_C_toricPoint.lean

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_WeierstrassGamma0Sqf
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open Polynomial

theorem ModularCurve.exists_isGamma0PowAt_tateBase_and_map_coeffMap_eq_prod_X_sub_C_toricPoint
    (F : Type u) [Field F] (p k : ℕ) [Fact p.Prime] (hpF : (p : F) ≠ 0) (n : ℕ) [NeZero n] :
    ∃ h : Polynomial (LaurentSeries F),
      ModularCurve.IsGamma0PowAt (ModularCurve.tateBase F n) p k h ∧
      ∀ (F' : Type v) [Field F'] (f : F →+* F') (ζ : F'), IsPrimitiveRoot ζ (p ^ k) →
        h.map (ModularCurve.coeffMap f) =
          ∏ a ∈ (Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a),
            (X - C (ModularCurve.toricPoint F' n (ζ ^ a)).1) := by sorry
