-- Prove2me | Theorems.Thm_ModularCurve_finiteDimensional_riemannRochSpace_weightDivisor
-- name    : ModularCurve.finiteDimensional_riemannRochSpace_weightDivisor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/935022df-7205-5dcf-81c3-d6c102dafbf1
-- title:
--   Finiteness of the weight divisor Riemann–Roch space
-- statement:
--   Let $p$ be a prime, let $K$ be an algebraically closed field of characteristic $p$, let $N$ be a nonzero natural number with $(N : K) \neq 0$, and let $m$ be a natural number. Write $F =$ `modularFunctionFieldC K N` for the intermediate field of the Laurent series field $K((q))$ generated over $K$ by the two series `jqModC K` and `jqNModC K N`. A place of $F$ over $K$ is a valuation subring of $F$ containing the image of $K$, distinct from $F$ itself, and a principal ideal ring; a divisor is a finitely supported function from places to $\mathbb{Z}$. The divisor `weightDivisor K N m` is a divisor whose value at each place $w$ equals $$\Big[\,0 < \operatorname{ord}_w(j)\,\Big]\left\lfloor \tfrac{2m\,\operatorname{ord}_w(j)}{3}\right\rfloor + \Big[\,0 < \operatorname{ord}_w(j-1728)\,\Big]\left\lfloor \tfrac{m\,\operatorname{ord}_w(j-1728)}{2}\right\rfloor + \Big[\,\operatorname{ord}_w(j) < 0\,\Big]\,m\,\operatorname{ord}_w(j),$$ where $j$ denotes the element `jqModC K` of $F$, provided such a finitely supported function exists, and is the zero divisor otherwise. The theorem asserts that the associated Riemann–Roch space, namely the $K$-submodule of $f \in F$ satisfying $v(f) \le \exp(D(v))$ for the adic valuation $v$ attached to every place, is a finite-dimensional $K$-vector space.
--
--   This is the standard finiteness of Riemann–Roch spaces on a one-variable function field with exact constant field, specialised to the weight-$m$ floor divisor on the level-$N$ modular function field. It supplies the finite-dimensional ambient spaces for the linear-algebra assembly behind the Hecke-operator computations, and is cited in the construction of [`ModularCurve.SSHeckeV2.ssHeckeFun_window`](thm.html#ModularCurve.SSHeckeV2.ssHeckeFun_window).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finiteDimensional_riemannRochSpace_weightDivisor.lean

import Mathlib
import Definitions.Def_ModularCurve_SSCarrier
import Definitions.Def_ModularCurve_SSHeckeV2
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_CuspForm_ModPForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open AlgebraicCurve ModularCurve

theorem ModularCurve.finiteDimensional_riemannRochSpace_weightDivisor
    (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] [IsAlgClosed K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) (m : ℕ) :
    FiniteDimensional K ↥(AlgebraicCurve.riemannRochSpace (ModularCurve.weightDivisor K N m)) := by sorry
