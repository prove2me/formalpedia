-- Prove2me | Theorems.Thm_ModularCurve_apply_mem_regularDifferentials_of_recipe
-- name    : ModularCurve.apply_mem_regularDifferentials_of_recipe
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/a4976ce0-b282-5897-9657-35976ce72b90
-- title:
--   Serre's dlog on p-torsion classes yields regular differentials
-- statement:
--   Let $K$ be a perfect field of characteristic $p$, $p$ prime, let $N$ be a nonzero natural number, and let $F =$ `modularFunctionFieldC K N` be the intermediate field of the Laurent series field $K((q))$ generated over $K$ by the two series `jqModC K` and `jqNModC K N`. Assume $F$ has characteristic $p$, is essentially of finite type over $K$, and is a curve over $K$ in the sense of `IsCurveOver`: every nonzero element of $F$ has a divisor of degree zero recording its orders at all places, every place has residue field finite over $K$, and $\Omega[F/K]$ is free of rank one over $F$; here a place is a valuation subring of $F$ containing the image of $K$, distinct from $F$ itself and a principal ideal ring, and divisors are the finitely supported $\mathbb{Z}$-valued functions on places. Assume further that at every place $w$ the element $w.\mathrm{dCoord} = d(\text{uniformizer})$ spans $\Omega[F/K]$ over $F$. Let $\delta$ be an additive map from the $p$-torsion subgroup of $\mathrm{Pic}^0(F) = (\text{degree-zero divisors})/(\text{principal divisors})$ to $\Omega[F/K]$ satisfying the following recipe: whenever $y$ is a $p$-torsion class, $E$ a degree-zero divisor whose class is $y$, and $g \in F$ nonzero with $p\,E(v) = \mathrm{ord}_v(g)$ at every place $v$, then $\delta y = g^{-1} \cdot D_{K,F}(g)$. The conclusion is that for every $p$-torsion class $y$, the differential $\delta y$ lies in `regularDifferentials K F`, that is, at each place $v$ it equals $f \cdot v.\mathrm{dCoord}$ for some $f$ in the valuation subring of $v$.
--
--   This is the regularity statement for the mod $p$ logarithmic derivative map $y \mapsto g^{-1}dg$ on $p$-torsion of the Jacobian of the modular curve, in the form used by Mazur, Wiles and Ribet: classes killed by $p$ give everywhere-regular differentials. It feeds the construction of the $\mathfrak m$-torsion differentials attached to Hecke torsion classes, being cited by [`ModularCurve.pullbackAlong_apply_mem_mTorsionDiffOf_of_mem_heckeTorsion_jZero_of_coe_eq_reductionModL`](thm.html#ModularCurve.pullbackAlong_apply_mem_mTorsionDiffOf_of_mem_heckeTorsion_jZero_of_coe_eq_reductionModL).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_apply_mem_regularDifferentials_of_recipe.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

open ModularCurve AlgebraicCurve

theorem ModularCurve.apply_mem_regularDifferentials_of_recipe
    (K : Type*) [Field K] [PerfectField K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (N : ℕ) [NeZero N] [IsCurveOver K (modularFunctionFieldC K N)] [Algebra.EssFiniteType K (modularFunctionFieldC K N)]
    [∀ w : Place K (modularFunctionFieldC K N), w.DCoordGenerates] [CharP (modularFunctionFieldC K N) p]
    (δ : Pic0.torsion K (modularFunctionFieldC K N) p →+ Ω[↥(modularFunctionFieldC K N)⁄K])
    (hδ : ∀ (y : Pic0.torsion K (modularFunctionFieldC K N) p)
        (E : Divisor.degZero (K := K) (F := modularFunctionFieldC K N)) (g : modularFunctionFieldC K N),
        Pic0.mk E = (y : Pic0 K (modularFunctionFieldC K N)) → g ≠ 0 →
        (∀ v : Place K (modularFunctionFieldC K N),
          (p : ℤ) * (E : Divisor K (modularFunctionFieldC K N)) v = v.ord g) →
        δ y = g⁻¹ • KaehlerDifferential.D K (modularFunctionFieldC K N) g)
    (y : Pic0.torsion K (modularFunctionFieldC K N) p) :
    δ y ∈ regularDifferentials K (modularFunctionFieldC K N) := by sorry
