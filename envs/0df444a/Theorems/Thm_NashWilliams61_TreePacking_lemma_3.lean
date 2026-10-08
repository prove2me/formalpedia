-- Prove2me | Theorems.Thm_NashWilliams61_TreePacking_lemma_3
-- name    : NashWilliams61.TreePacking.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:31:25.051957+00:00
-- url     : https://prove2.me/theorems/fafa70ce-9927-4a49-8b9b-d514be4ef620
-- title:
--   Lemma 3 — an $s$-good couple ($s \ge 1$) has an $(s-1)$-good $1$-supercouple
-- statement:
--   Let $G$ be a finite multigraph without loops on vertex set $V$, $k \ge 1$, and let $s$ be a positive integer. If $[G, g]$ is an $s$-good couple, then there are a new edge joining two distinct vertices of $V$ and a function $h : V \to \mathbb Z_{\ge 0}$ such that, with $H = G + \{\text{new edge}\}$,
--
--   1. $[H, h]$ is a $1$-supercouple of $[G, g]$, and
--   2. $[H, h]$ is $(s-1)$-good.
--
--   Iterating this lemma gives Corollary 3A.
--
--   **Formalization Note** $H$ has edge type $E \oplus \mathrm{Fin}\,1$; the new edge's ends are existentially quantified and must not form a loop. $\Delta_H$ is computed in $H$, so the new edge counts in $e_X$.
-- source:
--   Nash-Williams, Edge-disjoint spanning trees of finite graphs, J. London Math. Soc. 36 (1961), p. 446, Lemma 3

import Mathlib
import Definitions.Def_NagamochiIbaraki_EdgeConn_Multigraph
import Definitions.Def_NashWilliams61_TreePacking_Graphs
import Definitions.Def_NashWilliams61_TreePacking_Couples
open NagamochiIbaraki.EdgeConn

namespace NashWilliams61.TreePacking

/-- **Lemma 3** (Nash-Williams 1961, p. 446). If `s` is a positive integer, any `s`-good
couple `[G, g]` has an `(s − 1)`-good `1`-supercouple `[H, h]`, where `H = G + {new edge}`
has edge type `E ⊕ Fin 1`. -/
theorem lemma_3 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag) (k : ℕ) (hk : 0 < k)
    (g : V → ℕ) (s : ℕ) (hs : 0 < s) (hgood : IsGood k ends g s) :
    ∃ (a : Fin 1 → Sym2 V) (h : V → ℕ),
      IsSupercouple k ends g a h ∧ IsGood k (Sum.elim ends a) h (s - 1) := by sorry

end NashWilliams61.TreePacking
