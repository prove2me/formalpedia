-- Prove2me | Theorems.Thm_ModularCurve_ord_eq_zero_of_not_mem_ssPlacesQExp_of_hasValue_of_coe_eq_coeffMap_modularUnitSeries
-- name    : ModularCurve.ord_eq_zero_of_not_mem_ssPlacesQExp_of_hasValue_of_coe_eq_coeffMap_modularUnitSeries
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/b4cf0409-6a7b-5559-ab43-4134a68bde3c
-- title:
--   Reduction of Δ(q)/Δ(qᵖ) is a unit at ordinary affine places
-- statement:
--   Fix a prime $p$, an algebraically closed field $\kappa$ of characteristic $p$ and an arbitrary subgroup $\Gamma\le\mathrm{SL}_2(\mathbb Z)$, and work in the field $F=$ `qExpFunctionFieldC κ Γ`, the subfield of the Laurent series field $\kappa((q))$ generated over $\kappa$ by the quotients $p_f/p_g$ of integral $q$-expansions of modular forms for $\Gamma$ (`intFormRatiosC`). Let $x$ be a Laurent series with integer coefficients whose coefficientwise image in $\mathbb Q((q))$ under `coeffMap (Int.castRingHom ℚ)` is `modularUnitSeries p`, i.e. $\Delta(q)\cdot\Delta(q^p)^{-1}$ where $\Delta$ is the $\eta$-product Laurent series; let $g\in F$ have as its underlying Laurent series the coefficientwise reduction of $x$ into $\kappa((q))$. Let $v$ be a place of $F$ over $\kappa$, meaning a valuation subring of $F$ containing $\kappa$, not all of $F$, and a principal ideal ring. Assume $v\notin$ `ssPlacesQExp κ Γ p`, i.e. there is no element of $F$ with Laurent expansion `jqModC κ` (the reduction of the $q$-expansion $q^{-1}\cdot j\mathrm{Num}$ of $j$) having at $v$ a value lying in `ssJSet p κ`. Assume moreover that some $xj\in F$ has Laurent expansion `jqModC κ` and that $v$ has value $a\in\kappa$ at $xj$, in the sense that $xj$ lies in the valuation subring and its residue is the image of $a$ in the residue field. Then $\mathrm{ord}_v(g)=0$.
--
--   The element $g$ is the reduction in characteristic $p$ of Ogg's modular unit $\Delta(q)/\Delta(q^p)$, whose divisor on the reduced modular curve is supported on the supersingular points and the cusps; the statement records that it has order zero at every affine place at which the $j$-invariant takes a non-supersingular value. It is the complement, on the ordinary side, of the vanishing statement at supersingular places, and is used in the analysis of the de Rham model at $p$ of the curves $X_H$, in particular in the verification of the order conditions for fixed places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ord_eq_zero_of_not_mem_ssPlacesQExp_of_hasValue_of_coe_eq_coeffMap_modularUnitSeries.lean

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

theorem ModularCurve.ord_eq_zero_of_not_mem_ssPlacesQExp_of_hasValue_of_coe_eq_coeffMap_modularUnitSeries
    (p : ℕ) [Fact p.Prime] (κ : Type*) [Field κ] [CharP κ p] [IsAlgClosed κ] (Γ : Subgroup SL(2, ℤ))
    (x : LaurentSeries ℤ)
    (hx : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; coeffMap (Int.castRingHom ℚ) x = modularUnitSeries p)
    (g : ↥(qExpFunctionFieldC κ Γ)) (hg : ((g : ↥(qExpFunctionFieldC κ Γ)) : LaurentSeries κ) = coeffMap (Int.castRingHom κ) x)
    (v : Place κ ↥(qExpFunctionFieldC κ Γ)) (hv : v ∉ ssPlacesQExp κ Γ p)

    (xj : ↥(qExpFunctionFieldC κ Γ)) (hxj : ((xj : ↥(qExpFunctionFieldC κ Γ)) : LaurentSeries κ) = jqModC κ)
    (a : κ) (hva : v.HasValue (xj : ↥(qExpFunctionFieldC κ Γ)) a) :
    v.ord (g : ↥(qExpFunctionFieldC κ Γ)) = 0 := by sorry
