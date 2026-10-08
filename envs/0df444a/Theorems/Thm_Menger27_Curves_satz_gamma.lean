-- Prove2me | Theorems.Thm_Menger27_Curves_satz_gamma
-- name    : Menger27.Curves.satz_gamma
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:15:16.118682+00:00
-- url     : https://prove2.me/theorems/42d40680-4059-460b-9854-ef3074e743c1
-- title:
--   Satz γ — nested closed separators remain separating
-- statement:
--   Let $R$ be a compact locally connected metric space with finitely many connected components. Let $A,B\subseteq R$ be disjoint closed sets. If $C_0\supseteq C_1\supseteq\cdots$ is a decreasing sequence of closed sets, each separating $A$ from $B$ in $R$, then
--   $$\bigcap_{k\ge0}C_k\text{ separates }A\text{ from }B\text{ in }R.$$
--
--   This permits passage from finite-stage separators to a limiting separator. **Formalization Note** The paper indexes from one; Lean indexes from zero. “Separates” allows a separator to meet $A$ or $B$, as on pp. 99–100.
-- source:
--   Menger, Zur allgemeinen Kurventheorie, Fund. Math. 10 (1927), p. 100, Satz γ

import Mathlib
import Definitions.Def_Menger27_Curves_Separation

namespace Menger27.Curves

/-- Satz γ, p. 100: a decreasing intersection of closed separators separates. -/
theorem satz_gamma {X : Type*} [MetricSpace X]
    [CompactSpace X] [LocallyConnectedSpace X]
    [Finite (ConnectedComponents X)]
    (A B : Set X) (hA : IsClosed A) (hB : IsClosed B)
    (hdisj : Disjoint A B) (C : ℕ → Set X)
    (hclosed : ∀ k, IsClosed (C k))
    (hnested : ∀ k, C (k + 1) ⊆ C k)
    (hsep : ∀ k, Separates Set.univ (C k) A B) :
    Separates Set.univ (⋂ k, C k) A B := by sorry

end Menger27.Curves
