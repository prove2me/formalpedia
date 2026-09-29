-- Prove2me | Theorems.Thm_ModularCurve_exists_divisor_forall_eq_weightFloor_fieldC
-- name    : ModularCurve.exists_divisor_forall_eq_weightFloor_fieldC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/c7074e24-c92b-5229-9e3f-94b325142c05
-- title:
--   Finite support of the weight floor on K(jmath̄,jmath̄_N)
-- statement:
--   Let $K$ be a perfect field, let $N\ge 1$ be a natural number and let $m$ be a natural number. Write $F=$ `modularFunctionFieldC K N` for the intermediate field of the Laurent series field $K((q))$ generated over $K$ by the two elements `jqModC K` (the integral $j$-series $q^{-1}\cdot\mathrm{jNum}$ with coefficients pushed into $K$) and `jqNModC K N` (its image under the $q\mapsto q^N$ expansion operator `qExpand K N`). A place of $F/K$ is, by definition, a valuation subring of $F$ containing the image of $K$, distinct from $F$ itself, and a principal ideal ring; a divisor is a finitely supported function from places to $\mathbb{Z}$. Put $j=$ `jqModC K` viewed as an element of $F$. The assertion is that there exists a divisor $D$ of $F/K$ such that for every place $w$ of $F/K$ one has $D(w)=$ `weightFloor K N m w`, the integer
--   $$\big[\operatorname{ord}_w j>0\big]\cdot\big(2m\operatorname{ord}_w j\big)/3+\big[\operatorname{ord}_w(j-1728)>0\big]\cdot\big(m\operatorname{ord}_w(j-1728)\big)/2+\big[\operatorname{ord}_w j<0\big]\cdot m\operatorname{ord}_w j,$$
--   where each bracket denotes the indicator of the stated condition, $\operatorname{ord}_w$ is the order function of the place, and the two quotients are integer division (the numerators being non‑negative in the relevant branches, this is the floor). In other words, the function $w\mapsto$ `weightFloor K N m w` has finite support.
--
--   The displayed function is the floor divisor attached to weight $2m$ on the level‑$N$ modular function field, built from the orders of vanishing of $\bar\jmath$ at $0$, of $\bar\jmath-1728$ at the elliptic points of order $2$, and of the pole of $\bar\jmath$ at the cusps. The statement supplies the finiteness needed to define the divisor `weightDivisor` with these prescribed values, and is used in the Riemann–Roch estimates for spaces of mod $p$ modular forms and their Hecke eigenvectors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_divisor_forall_eq_weightFloor_fieldC.lean

import Mathlib
import Definitions.Def_ModularCurve_WeightDivisor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open ModularCurve

theorem ModularCurve.exists_divisor_forall_eq_weightFloor_fieldC
    (K : Type*) [Field K] [PerfectField K] (N : ℕ) [NeZero N] (m : ℕ) :
    ∃ D : Divisor K ↥(modularFunctionFieldC K N), ∀ w : Place K ↥(modularFunctionFieldC K N),
      D w = weightFloor K N m w := by sorry
