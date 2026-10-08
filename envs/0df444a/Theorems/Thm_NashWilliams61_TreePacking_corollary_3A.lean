-- Prove2me | Theorems.Thm_NashWilliams61_TreePacking_corollary_3A
-- name    : NashWilliams61.TreePacking.corollary_3A
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:31:41.688709+00:00
-- url     : https://prove2.me/theorems/5c04e157-6557-40c5-aea8-66047ea58cad
-- title:
--   Corollary 3A — any $s$-good couple has an $s$-supercouple
-- statement:
--   Let $G$ be a finite multigraph without loops on vertex set $V$, $k \ge 1$, and $s \ge 0$. If $[G, g]$ is an $s$-good couple, then one can add $s$ new edges, none of them a loop, to obtain a graph $H$, and choose $h : V \to \mathbb Z_{\ge 0}$, such that $[H, h]$ is an $s$-supercouple of $[G, g]$: $[H, h]$ is a couple ($\Delta_H(X) \ge 0$ for all non-empty $X$) and every vertex $\xi$ is incident with exactly $g(\xi) - h(\xi)$ of the new edges.
--
--   In the proof of Theorem 1 this is applied to $[Z^*, f]$, where $Z = V(G) \setminus \{\xi\}$ and $f(\eta)$ counts the edges between $\xi$ and $\eta$.
--
--   **Formalization Note** $H$ has edge type $E \oplus \mathrm{Fin}\,s$. The conclusion is that $[H,h]$ is an $s$-supercouple (in particular a couple), not that it is good. For $s = 0$ the empty family of new edges and $h = g$ are allowed.
-- source:
--   Nash-Williams, Edge-disjoint spanning trees of finite graphs, J. London Math. Soc. 36 (1961), p. 447, Corollary 3A

import Mathlib
import Definitions.Def_NagamochiIbaraki_EdgeConn_Multigraph
import Definitions.Def_NashWilliams61_TreePacking_Graphs
import Definitions.Def_NashWilliams61_TreePacking_Couples
open NagamochiIbaraki.EdgeConn

namespace NashWilliams61.TreePacking

/-- **Corollary 3A** (Nash-Williams 1961, p. 447). Any `s`-good couple `[G, g]` has an
`s`-supercouple `[H, h]`, where `H` is `G` plus `s` new edges (edge type `E ⊕ Fin s`). -/
theorem corollary_3A {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag) (k : ℕ) (hk : 0 < k)
    (g : V → ℕ) (s : ℕ) (hgood : IsGood k ends g s) :
    ∃ (a : Fin s → Sym2 V) (h : V → ℕ), IsSupercouple k ends g a h := by sorry

end NashWilliams61.TreePacking
