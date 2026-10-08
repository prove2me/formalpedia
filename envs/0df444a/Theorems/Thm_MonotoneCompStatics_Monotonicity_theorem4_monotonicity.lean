-- Prove2me | Theorems.Thm_MonotoneCompStatics_Monotonicity_theorem4_monotonicity
-- name    : MonotoneCompStatics.Monotonicity.theorem4_monotonicity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:33:45.011694+00:00
-- url     : https://prove2.me/theorems/58cb3d9d-2ba2-408b-90eb-b8d67f28a8e3
-- title:
--   Theorem 4 (Monotonicity Theorem)
-- statement:
--   Let $X$ be a lattice, $T$ a partially ordered set, and $f:X\times T\to\mathbb R$. For every constraint set $S\subseteq X$, write $M(t,S)=\operatorname{argmax}_{x\in S}f(x,t)$. Then $M$ is monotone nondecreasing jointly in the parameter and constraint set if and only if $f(\cdot,t)$ is quasisupermodular on $X$ for every $t$ and $f$ has the single crossing property in $(x;t)$:
--
--   $$\bigl[\forall t\le t',\ S\le_s S':\ M(t,S)\le_s M(t',S')\bigr]\quad\Longleftrightarrow\quad\bigl[\forall t,\ f(\cdot,t)\text{ is quasisupermodular}\bigr]\ \land\ \bigl[f\text{ has single crossing}\bigr].$$
--
--   This equivalence characterizes monotone comparative statics without requiring cardinal supermodularity or increasing differences.
--
--   **Formalization Note** $f$ is curried in Lean. The strong set order is the published lattice relation, and all constraint sets, including empty ones, are quantified. Quasisupermodularity and single crossing each include a weak and a strict implication; the latter compares strictly ordered choices and parameters.
-- source:
--   Milgrom and Shannon, Monotone Comparative Statics, Econometrica 62 (1994), p. 162 (PDF 7), Theorem 4 (Monotonicity Theorem)

import Mathlib
import Definitions.Def_MonotoneCompStatics_Monotonicity_ArgmaxMonotone
import Definitions.Def_MonotoneCompStatics_Monotonicity_QuasiSupermodularOn
import Definitions.Def_MonotoneCompStatics_Monotonicity_SingleCrossing

namespace MonotoneCompStatics.Monotonicity

theorem theorem4_monotonicity {X T : Type*} [Lattice X] [PartialOrder T] (f : X → T → ℝ) :
    ArgmaxMonotone f ↔ (∀ t, QuasiSupermodularOn (fun x => f x t) Set.univ) ∧ SingleCrossing f := by sorry

end MonotoneCompStatics.Monotonicity
