-- Prove2me | Theorems.Thm_LieTwoAlg_Equiv_lemma_6
-- name    : LieTwoAlg.Equiv.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:25:37.129137+00:00
-- url     : https://prove2.me/theorems/d0cb8273-a81e-46e7-940e-932ede0adeff
-- title:
--   Lemma 6, p. 9 — composition in a 2-vector space is forced
-- statement:
--   Let $V$ be a $2$-vector space over any field. For composable $f$ and $g$, the linear formula $fg=f+g-i(t(f))$ has source $s(f)$ and target $t(g)$. It is associative and obeys both identity laws. Moreover, any linear composition on the pullback of composable pairs that obeys the identity laws equals this formula:
--
--   $$
--   (f,g)\in V_1\times_{V_0}V_1\quad\Longrightarrow\quad fg=f+g-i(t(f)).
--   $$
--
--   Thus source, target, and identity determine the entire internal-category composition, as Lemma 6 asserts. The uniqueness clause concerns a linear map on the pullback, not an arbitrary binary operation.
-- source:
--   Baez–Crans, Higher-Dimensional Algebra VI: Lie 2-Algebras, arXiv:math/0307263v6, pp. 9–11, Lemma 6

import Mathlib
import Definitions.Def_LieTwoAlg_Equiv_Model

namespace LieTwoAlg.Equiv

universe u

/-- Lemma 6, pp. 9–11: the forced linear composition and its category laws. -/
theorem lemma_6 {k : Type u} [Field k] (V : TwoVect k) :
    (∀ f g : V.V1, V.t f = V.s g →
      V.s (V.comp f g) = V.s f ∧ V.t (V.comp f g) = V.t g) ∧
    (∀ f g h : V.V1, V.comp (V.comp f g) h = V.comp f (V.comp g h)) ∧
    (∀ f : V.V1, V.comp (V.i (V.s f)) f = f ∧
      V.comp f (V.i (V.t f)) = f) ∧
    (∀ c : V.composable →ₗ[k] V.V1,
      (∀ f : V.V1, c (V.leftUnitPair f) = f) →
      (∀ f : V.V1, c (V.rightUnitPair f) = f) →
      ∀ p : V.composable, c p = V.comp p.1.1 p.1.2) := by sorry

end LieTwoAlg.Equiv
