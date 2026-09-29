-- Prove2me | Theorems.Thm_ModularCurve_diamondActionModL_apply_eq_self_of_coe_eq_coeffMap_modularUnitSeries
-- name    : ModularCurve.diamondActionModL_apply_eq_self_of_coe_eq_coeffMap_modularUnitSeries
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/bc10cefa-2459-59c0-9637-bd068801840e
-- title:
--   Diamond operators fix the mod p reduction of Δ(q)/Δ(qᵖ)
-- statement:
--   Fix a prime $p$, an algebraically closed field $\kappa$ of characteristic $p$, an integer $N \neq 0$, a subgroup $H' \le (\mathbb{Z}/N)^\times$, and an element $d$ of $\Gamma_0(N)$. Let $x$ be a Laurent series with integer coefficients whose coefficientwise image under $\mathbb{Z} \to \mathbb{Q}$ (the map `coeffMap (Int.castRingHom ℚ)`) is `modularUnitSeries p`, that is, the series $\Delta = q\cdot\eta\text{-unit}(q)$ divided by its substitution $q \mapsto q^p$, so $x$ is an integral model of $\Delta(q)/\Delta(q^p)$. Let $g$ belong to `qExpFunctionFieldC κ (CohCarrier.GammaH N H')`, the intermediate field of $\kappa((q))$ generated over $\kappa$ by the ratios $\mathrm{intSeriesC}\,\kappa\,p_f / \mathrm{intSeriesC}\,\kappa\,p_g$ of integral $q$-expansions of modular forms of a common weight for the subgroup of $SL(2,\mathbb{Z})$ obtained by pushing forward the preimage of $H'$ under the determinant-type character `gamma0Units N` of $\Gamma_0(N)$; assume the Laurent series underlying $g$ is the coefficientwise reduction of $x$ along $\mathbb{Z} \to \kappa$. Then $g$ is fixed by the diamond operator attached to $d$: `diamondActionModL κ N H' d g = g`, where `diamondActionModL` is a chosen homomorphism from $\Gamma_0(N)$ to the $\kappa$-algebra automorphisms of this field satisfying `IsDiamondPullbackModL` when such a homomorphism exists, and the trivial homomorphism otherwise.
--
--   The series $\Delta(q)/\Delta(q^p)$ is Ogg's modular unit; in characteristic $p$ its reduction lies in the level-one part of the function field, and the assertion is that the Galois action of $\Gamma_0(N)/\Gamma_{H'}(N)$ by diamond operators leaves it untouched. It is used in the analysis of the de Rham model at $p$ of $X_{H}$, where invariance of this unit under the diamonds transfers to invariance of its divisor and of the associated one-sided differential data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_diamondActionModL_apply_eq_self_of_coe_eq_coeffMap_modularUnitSeries.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve
open scoped MatrixGroups

theorem ModularCurve.diamondActionModL_apply_eq_self_of_coe_eq_coeffMap_modularUnitSeries
    (p : ℕ) [Fact p.Prime] (κ : Type*) [Field κ] [CharP κ p] [IsAlgClosed κ]
    (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ) (d : CongruenceSubgroup.Gamma0 N)
    (x : LaurentSeries ℤ)
    (hx : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; coeffMap (Int.castRingHom ℚ) x = modularUnitSeries p)
    (g : ↥(qExpFunctionFieldC κ (CohCarrier.GammaH N H'))) (hg : ((g : ↥(qExpFunctionFieldC κ (CohCarrier.GammaH N H'))) : LaurentSeries κ) = coeffMap (Int.castRingHom κ) x) :
    diamondActionModL κ N H' d g = g := by sorry
