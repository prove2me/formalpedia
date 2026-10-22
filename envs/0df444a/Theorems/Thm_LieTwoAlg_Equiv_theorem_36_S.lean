-- Prove2me | Theorems.Thm_LieTwoAlg_Equiv_theorem_36_S
-- name    : LieTwoAlg.Equiv.theorem_36_S
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:25:51.883984+00:00
-- url     : https://prove2.me/theorems/2f2fb7af-6328-4073-a77b-24535ed234d2
-- title:
--   Proof of Theorem 36, p. 36 — construction S
-- statement:
--   For every semistrict Lie $2$-algebra $L$ over the fixed field, $S(L)$ is a two-term $L_\infty$-algebra with
--
--   $$
--   V_0=L_0,\quad V_1=\ker s,\quad d=t|_{\ker s},\quad l_2(x,h)=\overrightarrow{[1_x,h]},\quad l_3(x,y,z)=\vec J_{x,y,z}.
--   $$
--
--   For every lawful Lie $2$-algebra homomorphism $F:L\to M$, the construction $S(F)$ is an $L_\infty$-homomorphism. Its chain map is obtained by restricting $F$ to the arrow parts, and its comparison map is $\varphi_2(x,y)=\vec F_2(x,y)$.
--
--   This milestone checks the paper's reverse construction on objects and morphisms; functoriality and the natural isomorphisms belong to the final goal.
-- source:
--   Baez–Crans, Higher-Dimensional Algebra VI: Lie 2-Algebras, arXiv:math/0307263v6, pp. 34–36, proof of Theorem 36, construction S

import Mathlib
import Definitions.Def_LieTwoAlg_Equiv_Model

namespace LieTwoAlg.Equiv

universe u

/-- Proof of Theorem 36, pp. 34–36: S on objects and morphisms. -/
theorem theorem_36_S {k : Type u} [Field k] (h2 : (2 : k) ≠ 0) :
    (∀ (L : Lie2Data k), IsLie2 L → IsLInf (toLInf L)) ∧
    (∀ {L M : Lie2Data k} (F : Lie2Hom L M),
      IsLie2 L → IsLie2 M → IsLie2Hom F → IsLInfHom (toLInfHom F)) := by sorry

end LieTwoAlg.Equiv
