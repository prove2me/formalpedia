-- Prove2me | Theorems.Thm_MonotoneCompStatics_Monotonicity_corollary2
-- name    : MonotoneCompStatics.Monotonicity.corollary2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:31:38.26836+00:00
-- url     : https://prove2.me/theorems/09c6bdca-24e5-4dd4-b57c-354b86be6f09
-- title:
--   Corollary 2: maximizers form a sublattice
-- statement:
--   Let $X$ be a lattice, let $S\subseteq X$ be a sublattice, and let $g:X\to\mathbb R$ be quasisupermodular. Then the maximizer set is a sublattice contained in $S$:
--
--   $$\operatorname{argmax}_{x\in S}g(x)\subseteq S,\qquad \operatorname{argmax}_{x\in S}g(x)\text{ is closed under }\wedge\text{ and }\vee.$$
--
--   This describes the order structure of optimizers, even when no optimizer exists.
--
--   **Formalization Note** The paper writes $f(x,t)$; this statement fixes an arbitrary parameter $t$ and calls the resulting function $g$. The empty maximizer set counts as a sublattice because closure is vacuous.
-- source:
--   Milgrom and Shannon, Monotone Comparative Statics, Econometrica 62 (1994), p. 163 (PDF 8), Corollary 2

import Mathlib
import Definitions.Def_MonotoneCompStatics_Monotonicity_argmaxOn
import Definitions.Def_MonotoneCompStatics_Monotonicity_QuasiSupermodularOn

namespace MonotoneCompStatics.Monotonicity

theorem corollary2 {X : Type*} [Lattice X] (g : X → ℝ) (S : Set X)
    (hS : IsSublattice S) (hq : QuasiSupermodularOn g Set.univ) :
    IsSublattice (argmaxOn g S) ∧ argmaxOn g S ⊆ S := by sorry

end MonotoneCompStatics.Monotonicity
