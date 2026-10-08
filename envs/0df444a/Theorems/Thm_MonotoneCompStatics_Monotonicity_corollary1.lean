-- Prove2me | Theorems.Thm_MonotoneCompStatics_Monotonicity_corollary1
-- name    : MonotoneCompStatics.Monotonicity.corollary1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:31:35.80032+00:00
-- url     : https://prove2.me/theorems/7704e610-c343-49c3-8edf-a69a613f3925
-- title:
--   Corollary 1: quasisupermodularity and monotonicity in the constraint set
-- statement:
--   Let $X$ be a lattice and $g:X\to\mathbb R$. The function $g$ is quasisupermodular on $X$ if and only if its maximizer set is nondecreasing under the strong set order as the constraint set rises:
--
--   $$g\text{ is quasisupermodular}\quad\Longleftrightarrow\quad\bigl[S\le_s S'\Rightarrow\operatorname{argmax}_{x\in S}g(x)\le_s\operatorname{argmax}_{x\in S'}g(x)\text{ for all }S,S'\subseteq X\bigr].$$
--
--   This isolates the choice-set part of Theorem 4 when there is no varying parameter.
--
--   **Formalization Note** The statement ranges over all constraint sets, including empty ones, and uses the paper's strong set order.
-- source:
--   Milgrom and Shannon, Monotone Comparative Statics, Econometrica 62 (1994), p. 163 (PDF 8), Corollary 1

import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder
import Definitions.Def_MonotoneCompStatics_Monotonicity_argmaxOn
import Definitions.Def_MonotoneCompStatics_Monotonicity_QuasiSupermodularOn

namespace MonotoneCompStatics.Monotonicity

theorem corollary1 {X : Type*} [Lattice X] (g : X → ℝ) :
    QuasiSupermodularOn g Set.univ ↔
      ∀ ⦃S S' : Set X⦄, Supermodularity.Lattices.InducedSetOrder S S' →
        Supermodularity.Lattices.InducedSetOrder (argmaxOn g S) (argmaxOn g S') := by sorry

end MonotoneCompStatics.Monotonicity
