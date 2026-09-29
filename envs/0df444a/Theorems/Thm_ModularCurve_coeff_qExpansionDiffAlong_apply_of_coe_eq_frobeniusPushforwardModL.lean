-- Prove2me | Theorems.Thm_ModularCurve_coeff_qExpansionDiffAlong_apply_of_coe_eq_frobeniusPushforwardModL
-- name    : ModularCurve.coeff_qExpansionDiffAlong_apply_of_coe_eq_frobeniusPushforwardModL
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/9d207632-ee54-54c7-858e-59240701017c
-- title:
--   Frobenius push-forward p-th powers the q-expansion coefficients of δ
-- statement:
--   Let $K$ be an algebraically closed field of characteristic a prime $p$, let $N\ge 1$, and let $F=$ `modularFunctionFieldFullC K N` be the intermediate field of the Laurent series field $K((q))$ generated over $K$ by the series $q\mapsto \tilde\jmath(q^{d})$ for the divisors $d\mid N$ (the set `divisorExpansionsC`). Here $\operatorname{Pic}^0_K(F)$ is the group of degree-zero divisors on the places of $F$ over $K$ modulo principal divisors, and `Pic0.torsion K F p` is its subgroup killed by $p$. Assume given an additive map $\delta$ from that $p$-torsion subgroup to $\Omega_{F/K}$ satisfying Serre's recipe: whenever $y$ is a $p$-torsion class, $E$ a degree-zero divisor with $\mathrm{Pic}^0$-class $y$, and $g\in F$ is nonzero with $p\,E(v)=\operatorname{ord}_v(g)$ at every place $v$, then $\delta y=g^{-1}\,dg$. Let $x,y$ be $p$-torsion classes whose images in $\operatorname{Pic}^0_K(F)$ satisfy $y=\mathrm{Fr}_*x$, where $\mathrm{Fr}_*$ is `frobeniusPushforwardModL K N p`, i.e. the endomorphism induced on $\operatorname{Pic}^0$ by divisor push-forward along `frobeniusModL K N p` when the package `FrobeniusInputsModL` (existence of principal divisors, finiteness along the Frobenius map, the fundamental identity and the norm formula) holds, and the zero map otherwise. Then for every $n\in\mathbb Z$ the $n$-th coefficient of the $q$-expansion of $\delta y$ along the inclusion $F\hookrightarrow K((q))$ equals the $p$-th power of the $n$-th coefficient of the $q$-expansion of $\delta x$; here the $q$-expansion of a differential is the $K$-linear map $\Omega_{F/K}\to K((q))$ characterised by sending $dx$ to the formal derivative-type series $\theta$ of the expansion of $x$ and by $F$-semilinearity along the inclusion (the chosen map `qExpansionDiffAlong`, zero if no such map exists).
--
--   This is the $q$-expansion form of Serre's observation that the $\mathrm{dlog}$ map $\delta$ on the $p$-torsion of the Jacobian in characteristic $p$ intertwines the geometric Frobenius push-forward with the coefficientwise $p$-th power on Laurent expansions. It feeds the identification of the Frobenius push-forward with the Hecke operator $U_p$ on $q$-expansions in the mod-$p$ theory of the modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coeff_qExpansionDiffAlong_apply_of_coe_eq_frobeniusPushforwardModL.lean

import Mathlib
import Definitions.Def_ModularCurve_FrobeniusModL
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

open ModularCurve AlgebraicCurve

theorem ModularCurve.coeff_qExpansionDiffAlong_apply_of_coe_eq_frobeniusPushforwardModL
    (K : Type*) [Field K] [IsAlgClosed K] {p : ℕ} [Fact p.Prime] [CharP K p] (N : ℕ) [NeZero N]
    (δ : Pic0.torsion K (modularFunctionFieldFullC K N) p →+ Ω[↥(modularFunctionFieldFullC K N)⁄K])
    (hδ : ∀ (y : Pic0.torsion K (modularFunctionFieldFullC K N) p)
        (E : Divisor.degZero (K := K) (F := modularFunctionFieldFullC K N)) (g : modularFunctionFieldFullC K N),
        Pic0.mk E = (y : Pic0 K (modularFunctionFieldFullC K N)) → g ≠ 0 →
        (∀ v : Place K (modularFunctionFieldFullC K N),
          (p : ℤ) * (E : Divisor K (modularFunctionFieldFullC K N)) v = v.ord g) →
        δ y = g⁻¹ • KaehlerDifferential.D K (modularFunctionFieldFullC K N) g)
    (x y : Pic0.torsion K (modularFunctionFieldFullC K N) p)
    (hy : (y : Pic0 K (modularFunctionFieldFullC K N)) =
      frobeniusPushforwardModL K N p (x : Pic0 K (modularFunctionFieldFullC K N))) (n : ℤ) :
    (qExpansionDiffAlong (modularFunctionFieldFullC K N).val (δ y)).coeff n =
      ((qExpansionDiffAlong (modularFunctionFieldFullC K N).val (δ x)).coeff n) ^ p := by sorry
