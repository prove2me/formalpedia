-- Prove2me | Theorems.Thm_ModularCurve_exists_divisor_forall_eq_weightFloor
-- name    : ModularCurve.exists_divisor_forall_eq_weightFloor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/328678ff-c7d9-59a1-8d0a-96e37b5c3da8
-- title:
--   Existence of the weight-2m floor divisor
-- statement:
--   Let $K$ be a perfect field, let $N$ be a nonzero natural number and let $m$ be a natural number. Write $F$ = `modularFunctionFieldFullC K N` for the intermediate field of $K((q)) =$ `LaurentSeries K` generated over $K$ by the set of all $q$-expansions `qExpand K d (jqModC K)` for nonzero divisors $d \mid N$, where `jqModC K` $= q^{-1}\cdot(E_4^3\,\eta^{-24})$ is the image in $K((q))$ of the $q$-expansion of the $j$-invariant, and let $j \in F$ denote the element `jqModC K` itself. A place of $F/K$ is a valuation subring of $F$ containing $K$, different from $F$, and a principal ideal ring, and $\mathrm{ord}_w$ is the associated normalised valuation. The assertion is that there is a divisor $D$ of $F/K$, i.e. a finitely supported function from places of $F/K$ to $\mathbb{Z}$, whose value at every place $w$ equals
--   $$\Big[\mathrm{ord}_w j>0\Big]\,\frac{2m\,\mathrm{ord}_w j}{3} \;+\; \Big[\mathrm{ord}_w(j-1728)>0\Big]\,\frac{m\,\mathrm{ord}_w(j-1728)}{2} \;+\; \Big[\mathrm{ord}_w j<0\Big]\,m\,\mathrm{ord}_w j,$$
--   where $1728$ means the image of $1728 \in K$ in $F$, each bracket is $1$ when the condition holds and $0$ otherwise, and the two fractions are integer quotients by $3$ and by $2$, which in the branches concerned (non-negative numerator) are the floors of the corresponding rationals.
--
--   This is the weight-$2m$ floor divisor $D_{2m}$ attached to the full level-$N$ modular function field: its Riemann–Roch space is the space of mod-$p$ modular forms of weight $2m$ read as functions $f/(dj)^m$, the three terms recording the elliptic points of order $3$ and $2$ and the cusps. It is used to produce the divisor whose Riemann–Roch bound yields the dimension estimate in [`ModularCurve.exists_linearIndependent_isModPFormFn_algebraicClosure_dimFormula_le_card`](thm.html#ModularCurve.exists_linearIndependent_isModPFormFn_algebraicClosure_dimFormula_le_card); only the existence of a finitely supported function with the prescribed values is asserted here, not any geometric property of $D$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_divisor_forall_eq_weightFloor.lean

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_ModPFormFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open ModularCurve

theorem ModularCurve.exists_divisor_forall_eq_weightFloor
    (K : Type) [Field K] [PerfectField K] (N : ℕ) [NeZero N] (m : ℕ) :
    ∃ D : Divisor K ↥(modularFunctionFieldFullC K N), ∀ w : Place K ↥(modularFunctionFieldFullC K N),
      D w = (if 0 < w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N))
               then (2 * (m : ℤ) * w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N))) / 3 else 0)
          + (if 0 < w.ord ((⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) - algebraMap K _ 1728)
               then ((m : ℤ) * w.ord ((⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) - algebraMap K _ 1728)) / 2 else 0)
          + (if w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) < 0
               then (m : ℤ) * w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) else 0) := by sorry
