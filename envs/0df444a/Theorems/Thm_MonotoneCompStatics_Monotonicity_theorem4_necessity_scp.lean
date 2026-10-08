-- Prove2me | Theorems.Thm_MonotoneCompStatics_Monotonicity_theorem4_necessity_scp
-- name    : MonotoneCompStatics.Monotonicity.theorem4_necessity_scp
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:33:24.285069+00:00
-- url     : https://prove2.me/theorems/d10d7fc2-d10e-4dfa-994c-57518a4c6e2b
-- title:
--   Theorem 4, proof (⇒): monotonicity implies single crossing
-- statement:
--   Let $X$ be a lattice, $T$ a partially ordered set, and $f:X\times T\to\mathbb R$. If its maximizers are nondecreasing in $(t,S)$ under the strong set order, then whenever $x''<x'$ and $t''<t'$, both preference implications hold:
--
--   $$f(x'',t'')<f(x',t'')\Rightarrow f(x'',t')<f(x',t'),\qquad f(x'',t'')\le f(x',t'')\Rightarrow f(x'',t')\le f(x',t').$$
--
--   This is the parameter part of the necessity argument in Theorem 4.
--
--   **Formalization Note** The strict and weak implications are both part of single crossing; maximizer monotonicity is required over every constraint set, including the two-point set in the paper's argument.
-- source:
--   Milgrom and Shannon, Monotone Comparative Statics, Econometrica 62 (1994), p. 162 (PDF 7), Theorem 4, proof (⇒), single crossing

import Mathlib
import Definitions.Def_MonotoneCompStatics_Monotonicity_ArgmaxMonotone
import Definitions.Def_MonotoneCompStatics_Monotonicity_SingleCrossing

namespace MonotoneCompStatics.Monotonicity

theorem theorem4_necessity_scp {X T : Type*} [Lattice X] [PartialOrder T] (f : X → T → ℝ)
    (hm : ArgmaxMonotone f) :
    SingleCrossing f := by sorry

end MonotoneCompStatics.Monotonicity
