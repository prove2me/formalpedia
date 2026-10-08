-- Prove2me | Theorems.Thm_MonotoneCompStatics_Monotonicity_theorem4_necessity_qsm
-- name    : MonotoneCompStatics.Monotonicity.theorem4_necessity_qsm
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:35:03.972039+00:00
-- url     : https://prove2.me/theorems/910a3b74-781c-4bd4-9ebe-d3961e7bcc97
-- title:
--   Theorem 4, proof (⇒): monotonicity implies quasisupermodularity
-- statement:
--   Let $X$ be a lattice, $T$ a partially ordered set, and $f:X\times T\to\mathbb R$. If its maximizers are nondecreasing in the parameter and in the constraint set under the strong set order, then for every $t\in T$, the function $f(\cdot,t)$ is quasisupermodular on $X$:
--
--   $$f(x\wedge y,t)\le f(x,t)\Rightarrow f(y,t)\le f(x\vee y,t),\qquad f(x\wedge y,t)<f(x,t)\Rightarrow f(y,t)<f(x\vee y,t).$$
--
--   The constraint-set part of monotonicity therefore forces the ordinal complementarity condition.
--
--   **Formalization Note** Monotonicity ranges over all subsets of $X$, including the two-point sets used in the paper's necessity argument.
-- source:
--   Milgrom and Shannon, Monotone Comparative Statics, Econometrica 62 (1994), p. 162 (PDF 7), Theorem 4, proof (⇒), quasisupermodularity

import Mathlib
import Definitions.Def_MonotoneCompStatics_Monotonicity_ArgmaxMonotone
import Definitions.Def_MonotoneCompStatics_Monotonicity_QuasiSupermodularOn

namespace MonotoneCompStatics.Monotonicity

theorem theorem4_necessity_qsm {X T : Type*} [Lattice X] [PartialOrder T] (f : X → T → ℝ)
    (hm : ArgmaxMonotone f) :
    ∀ t, QuasiSupermodularOn (fun x => f x t) Set.univ := by sorry

end MonotoneCompStatics.Monotonicity
