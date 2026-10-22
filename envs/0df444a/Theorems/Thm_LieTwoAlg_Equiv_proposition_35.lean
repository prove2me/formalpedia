-- Prove2me | Theorems.Thm_LieTwoAlg_Equiv_proposition_35
-- name    : LieTwoAlg.Equiv.proposition_35
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:25:56.628322+00:00
-- url     : https://prove2.me/theorems/1137aac6-bd72-43b7-8e01-fdddcefc6e2d
-- title:
--   Proposition 35, p. 30 — the category 2TermL∞
-- statement:
--   Over the fixed field of characteristic different from $2$, two-term $L_\infty$-algebras and the homomorphisms of Definition 34 form a category. For lawful $\varphi:V\to W$ and $\psi:W\to X$, their composite is lawful, with
--
--   $$
--   (\varphi\psi)_2(x,y)=\psi_2(\varphi_0x,\varphi_0y)+\psi_1(\varphi_2(x,y)).
--   $$
--
--   The identity homomorphism has identity chain map and zero comparison. Composition is associative and satisfies both unit laws as equality of all homomorphism components.
--
--   This establishes the category used on the chain-complex side of Theorem 36.
-- source:
--   Baez–Crans, Higher-Dimensional Algebra VI: Lie 2-Algebras, arXiv:math/0307263v6, p. 30, Proposition 35

import Mathlib
import Definitions.Def_LieTwoAlg_Equiv_Model

namespace LieTwoAlg.Equiv

universe u

/-- Proposition 35, p. 30: the category laws of 2TermL∞. -/
theorem proposition_35 {k : Type u} [Field k] (h2 : (2 : k) ≠ 0) :
    (∀ {V W X : LInfData k} (hV : IsLInf V) (hW : IsLInf W) (hX : IsLInf X)
      (φ : LInfHom V W) (ψ : LInfHom W X),
      IsLInfHom φ → IsLInfHom ψ → IsLInfHom (φ.comp ψ)) ∧
    (∀ (V : LInfData k), IsLInf V → IsLInfHom (LInfHom.id V)) ∧
    (∀ {V W X Y : LInfData k} (φ : LInfHom V W) (ψ : LInfHom W X)
      (χ : LInfHom X Y), IsLInfHom φ → IsLInfHom ψ → IsLInfHom χ →
      (φ.comp ψ).comp χ = φ.comp (ψ.comp χ)) ∧
    (∀ {V W : LInfData k} (φ : LInfHom V W), IsLInfHom φ →
      (LInfHom.id V).comp φ = φ ∧ φ.comp (LInfHom.id W) = φ) := by sorry

end LieTwoAlg.Equiv
