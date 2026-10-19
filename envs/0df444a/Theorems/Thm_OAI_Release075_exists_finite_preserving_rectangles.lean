-- Prove2me | Theorems.Thm_OAI_Release075_exists_finite_preserving_rectangles
-- name    : OAI.Release075.exists_finite_preserving_rectangles
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:37:47.806315+00:00
-- url     : https://prove2.me/theorems/6eb9e4b8-3bc4-45a6-9e99-e068e4e667f3
-- title:
--   Residual finiteness preserves finitely many rectangle words
-- statement:
--   Let $G$ be a residually finite group, $I$ a finite set, $r\in\mathbb N$, and $g:I\times[r]\times[r]\to G$ such that each $g_i$ has surviving rectangles:
--   $$
--   g_i(u,v)\,g_i(u',v)^{-1}\,g_i(u',v')\,g_i(u,v')^{-1}\ne1\qquad(u\ne u',\ v\ne v').
--   $$
--   Then there are a finite group $Q$ and a homomorphism $\varphi:G\to Q$ such that every $\varphi\circ g_i$ still has surviving rectangles.
--
--   Only finitely many rectangle words are involved, which is what makes one finite quotient suffice.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/MatrixRank.lean#L895-L912

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank

open OAI OAI.Release075
universe u v
open scoped BigOperators

theorem OAI.Release075.exists_finite_preserving_rectangles {I : Type u} {G : Type v} [Fintype I] [Group G]
    [Group.ResiduallyFinite G] {r : ℕ} (g : I → Fin r → Fin r → G)
    (hg : ∀ i, RectanglesSurvive (g i)) :
    ∃ (Q : Type (max u v)) (_ : Group Q) (_ : Fintype Q) (φ : G →* Q),
      ∀ i, RectanglesSurvive (fun u v => φ (g i u v)) := by sorry
