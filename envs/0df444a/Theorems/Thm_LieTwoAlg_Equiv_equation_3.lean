-- Prove2me | Theorems.Thm_LieTwoAlg_Equiv_equation_3
-- name    : LieTwoAlg.Equiv.equation_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:25:47.871849+00:00
-- url     : https://prove2.me/theorems/deeaf382-d7cb-421b-9fd7-aa75600cfe1b
-- title:
--   Equation (3), p. 32 — the two bracket formulas agree
-- statement:
--   Let $V$ be a two-term $L_\infty$-algebra over the paper's field, with $x,a\in V_0$ and arrow parts $f,g\in V_1$. The two decompositions of the morphism bracket in the construction $T(V)$ agree:
--
--   $$
--   -l_2(a,f)+l_2(x+df,g)=l_2(x,g)-l_2(a+dg,f).
--   $$
--
--   Here $l_2(a,f)$ is the degree $(0,1)$ bracket, while $l_2(f,a)=-l_2(a,f)$. The equality is equation (3), and supplies the compatibility needed for the bracket functor on morphisms.
-- source:
--   Baez–Crans, Higher-Dimensional Algebra VI: Lie 2-Algebras, arXiv:math/0307263v6, p. 32, equation (3)

import Mathlib
import Definitions.Def_LieTwoAlg_Equiv_Model

namespace LieTwoAlg.Equiv

universe u

/-- Equation (3), p. 32: the two descriptions of the bracket agree. -/
theorem equation_3 {k : Type u} [Field k] (h2 : (2 : k) ≠ 0)
    (V : LInfData k) (hV : IsLInf V)
    (x a : V.V0) (f g : V.V1) :
    -V.l2m a f + V.l2m (x + V.d f) g =
      V.l2m x g - V.l2m (a + V.d g) f := by sorry

end LieTwoAlg.Equiv
