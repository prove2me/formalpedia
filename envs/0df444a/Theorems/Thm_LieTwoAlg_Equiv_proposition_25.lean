-- Prove2me | Theorems.Thm_LieTwoAlg_Equiv_proposition_25
-- name    : LieTwoAlg.Equiv.proposition_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:25:47.095859+00:00
-- url     : https://prove2.me/theorems/2c08c8e4-3725-43a4-9b2b-cd9d73715842
-- title:
--   Proposition 25, p. 21 (1-cell part) — the category Lie2Alg
-- statement:
--   Semistrict Lie $2$-algebras and their homomorphisms form a category at the one-cell level. For lawful homomorphisms $F:L\to M$ and $G:M\to N$, their composite with comparison transformation
--
--   $$
--   (FG)_2(x,y)=G_2(F_0x,F_0y)\,G_1(F_2(x,y))
--   $$
--
--   is lawful. The identity on $L$ is lawful and has comparison $(1_L)_2(x,y)=i([x,y])$. Composition is associative and satisfies both unit laws as equality of all raw homomorphism data.
--
--   These are the category laws needed for Theorem 36. The source's additional $2$-homomorphism claims in Proposition 25 are outside this milestone.
-- source:
--   Baez–Crans, Higher-Dimensional Algebra VI: Lie 2-Algebras, arXiv:math/0307263v6, p. 21, Proposition 25, one-cell part

import Mathlib
import Definitions.Def_LieTwoAlg_Equiv_Model

namespace LieTwoAlg.Equiv

universe u

/-- Proposition 25, p. 21: the 1-cell category laws of Lie2Alg. -/
theorem proposition_25 {k : Type u} [Field k] :
    (∀ {L M N : Lie2Data k} (hL : IsLie2 L) (hM : IsLie2 M) (hN : IsLie2 N)
      (F : Lie2Hom L M) (G : Lie2Hom M N),
      IsLie2Hom F → IsLie2Hom G → IsLie2Hom (F.comp G)) ∧
    (∀ (L : Lie2Data k), IsLie2 L → IsLie2Hom (Lie2Hom.id L)) ∧
    (∀ {L M N P : Lie2Data k} (F : Lie2Hom L M) (G : Lie2Hom M N)
      (H : Lie2Hom N P), IsLie2Hom F → IsLie2Hom G → IsLie2Hom H →
      (F.comp G).comp H = F.comp (G.comp H)) ∧
    (∀ {L M : Lie2Data k} (F : Lie2Hom L M), IsLie2Hom F →
      (Lie2Hom.id L).comp F = F ∧ F.comp (Lie2Hom.id M) = F) := by sorry

end LieTwoAlg.Equiv
