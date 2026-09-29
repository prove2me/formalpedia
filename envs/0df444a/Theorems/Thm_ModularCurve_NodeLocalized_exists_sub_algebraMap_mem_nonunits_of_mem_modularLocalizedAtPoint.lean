-- Prove2me | Theorems.Thm_ModularCurve_NodeLocalized_exists_sub_algebraMap_mem_nonunits_of_mem_modularLocalizedAtPoint
-- name    : ModularCurve.NodeLocalized.exists_sub_algebraMap_mem_nonunits_of_mem_modularLocalizedAtPoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/6ea5cd31-b6d5-5db1-beef-0d2b67442e81
-- title:
--   Elements of the node-localized ring take A-values at W
-- statement:
--   Let $q$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb Q}$, let $k$ be a field of characteristic $q$ and let $\mathrm{red} \colon A \to k$ be a ring homomorphism whose zero set is exactly the maximal ideal of $A$ (i.e. $\mathrm{red}\,a = 0$ if and only if $a \in \mathrm{maximalIdeal}\,A$). Let $W$ be a place of $\overline{\mathbb Q} \subseteq$ `modularFunctionFieldBar (1 * q)` in the sense of the project's `Place` structure: a valuation subring of that field which contains the image of $\overline{\mathbb Q}$, is not the whole field, and is a principal ideal ring; $W.\mathrm{ord}$ denotes the associated additive order function coming from the adic valuation. Let $x, y \in A$ and assume that $j - x$ and $j_q - y$ have strictly positive order at $W$, where $j$ is `PlaceSpecialization.jFun` (the $q$-expansion of $j$, coefficients mapped into $\overline{\mathbb Q}$) and $j_q$ is `PlaceSpecialization.jqFun` (the corresponding series for $j$ composed with $q$-fold scaling), both viewed in `modularFunctionFieldBar (1 * q)`. Let $g$ be an element of `modularFunctionFieldBar (1 * q)` whose underlying Laurent series lies in `modularLocalizedAtPoint (1 * q) A.toSubring red (red x) (red y)`, i.e. there are two-variable polynomials $r, s$ over $A$ with `pointEval A red (red x) (red y) s` $\neq 0$ and $g \cdot$ `modularEval (1 * q) A s` $=$ `modularEval (1 * q) A r`, where `modularEval` and `pointEval` are the evaluation maps used in the definition of `modularLocalizedAtPoint`. Then there exists $a \in A$ such that $g - a$ lies in the nonunits of the valuation subring of $W$, that is, in its maximal ideal.
--
--   This says that a function regular at the point $(\mathrm{red}\,x, \mathrm{red}\,y)$ of the plane model of the modular curve of level $q$ is finite at any place $W$ where the coordinates $j, j_q$ are congruent to $x, y$, and that its value there may be taken in $A$. It is used in the treatment of crossing presentations at the supersingular-type points $j = 0$ and $j = 1728$, and in the construction of level-one prolongation pairs.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_NodeLocalized_exists_sub_algebraMap_mem_nonunits_of_mem_modularLocalizedAtPoint.lean

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_LevelOneProlongationPair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.NodeLocalized IsLocalRing

theorem ModularCurve.NodeLocalized.exists_sub_algebraMap_mem_nonunits_of_mem_modularLocalizedAtPoint
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (hker : ∀ a : A, red a = 0 ↔ a ∈ IsLocalRing.maximalIdeal A)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (x y : A)
    (hx : 0 < W.ord (PlaceSpecialization.jFun (q := q)
      - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ)))
    (hy : 0 < W.ord (PlaceSpecialization.jqFun (q := q)
      - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))
    (g : ↥(modularFunctionFieldBar (1 * q)))
    (hg : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈
      modularLocalizedAtPoint (1 * q) A.toSubring red (red x) (red y)) :
    ∃ a : A, g - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ)
      ∈ W.toValuationSubring.nonunits := by sorry
