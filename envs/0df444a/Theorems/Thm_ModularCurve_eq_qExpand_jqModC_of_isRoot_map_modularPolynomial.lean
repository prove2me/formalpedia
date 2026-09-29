-- Prove2me | Theorems.Thm_ModularCurve_eq_qExpand_jqModC_of_isRoot_map_modularPolynomial
-- name    : ModularCurve.eq_qExpand_jqModC_of_isRoot_map_modularPolynomial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/7101bb31-cce2-5c69-b35d-8711b88be393
-- title:
--   Uniqueness of the Laurent-series root of the modular equation Φₚ
-- statement:
--   Let $K$ be a field of characteristic zero and $p$ a prime. Let `data` be a `ModularPolynomialData p`, i.e. a polynomial $\Phi \in \mathbb{Z}[X][Y]$ together with the data that $\Phi$ is monic (in $Y$), that its degree equals $\sum_{d \mid p,\ d\ \text{squarefree}} p/d$, and that $\Phi$ evaluates to $0$ when its coefficients in $\mathbb{Z}[X]$ are evaluated at the $q$-expansion `jq` of $j$ and $Y$ is sent to the series `jqN p`. Let $r$ be a formal Laurent series over $K$ (a Hahn series over $\mathbb{Z}$ with coefficients in $K$), and suppose $r$ is a root of the one-variable polynomial over $K((q))$ obtained from $\Phi$ by mapping each coefficient in $\mathbb{Z}[X]$ into $K((q))$ along the ring homomorphism sending integers into $K((q))$ and $X$ to `jqModC K`, the series $q^{-1}$ times the image of the integral power series $E_4^3 \cdot \eta^{-24}$-numerator `jNum` in $K[[q]]$. The conclusion is that $r$ equals the image of `jqModC K` under `qExpand K p`, the ring endomorphism of $K((q))$ that multiplies all exponents by $p$; that is, $r = j(q^p)$.
--
--   This is the uniqueness half of the description of the roots of the modular equation of prime level: over a characteristic-zero field the only Laurent-series solution $Y$ of $\Phi_p(j(q), Y) = 0$ in $K((q))$ is $j(q^p)$. It is used in the analysis of automorphisms fixing the modular function field, via [`ModularCurve.algEquiv_eq_refl_of_forall_coe_eq_infSubgroup`](thm.html#ModularCurve.algEquiv_eq_refl_of_forall_coe_eq_infSubgroup).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_eq_qExpand_jqModC_of_isRoot_map_modularPolynomial.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial ModularCurve

theorem ModularCurve.eq_qExpand_jqModC_of_isRoot_map_modularPolynomial
    (K : Type*) [Field K] [CharZero K] (p : ℕ) [Fact p.Prime] (data : ModularCurve.ModularPolynomialData p)
    (r : LaurentSeries K)
    (hroot : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) (ModularCurve.jqModC K))).IsRoot r) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    r = ModularCurve.qExpand K p (ModularCurve.jqModC K) := by sorry
