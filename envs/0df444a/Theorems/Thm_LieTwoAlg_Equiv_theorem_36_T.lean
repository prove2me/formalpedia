-- Prove2me | Theorems.Thm_LieTwoAlg_Equiv_theorem_36_T
-- name    : LieTwoAlg.Equiv.theorem_36_T
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:25:44.740844+00:00
-- url     : https://prove2.me/theorems/eb25e96c-8de8-48ad-84d6-968a759445b8
-- title:
--   Proof of Theorem 36, p. 34 — construction T
-- statement:
--   For every two-term $L_\infty$-algebra $V$ over the fixed field, the construction $T(V)$ is a semistrict Lie $2$-algebra. It has objects $V_0$, arrows $V_0\oplus V_1$, morphism bracket
--
--   $$
--   [(x,f),(a,g)]=\bigl(l_2(x,a),-l_2(a,f)+l_2(x+df,g)\bigr),
--   $$
--
--   and Jacobiator $J_{x,y,z}=([[x,y],z],l_3(x,y,z))$. For every lawful $L_\infty$-homomorphism $\varphi:V\to W$, the construction $T(\varphi)$ is a Lie $2$-algebra homomorphism, with $F_2(x,y)=([\varphi_0x,\varphi_0y],\varphi_2(x,y))$.
--
--   This milestone checks the paper's construction on objects and morphisms; functoriality is part of the final equivalence goal.
-- source:
--   Baez–Crans, Higher-Dimensional Algebra VI: Lie 2-Algebras, arXiv:math/0307263v6, pp. 30–34, proof of Theorem 36, construction T

import Mathlib
import Definitions.Def_LieTwoAlg_Equiv_Model

namespace LieTwoAlg.Equiv

universe u

/-- Proof of Theorem 36, pp. 30–34: T on objects and morphisms. -/
theorem theorem_36_T {k : Type u} [Field k] (h2 : (2 : k) ≠ 0) :
    (∀ (V : LInfData k), IsLInf V → IsLie2 (ofLInf V)) ∧
    (∀ {V W : LInfData k} (φ : LInfHom V W),
      IsLInf V → IsLInf W → IsLInfHom φ → IsLie2Hom (ofLInfHom φ)) := by sorry

end LieTwoAlg.Equiv
