-- Prove2me | Theorems.Thm_MinCostArbPacking_Main_lemma_A_1
-- name    : MinCostArbPacking.Main.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:42:35.775234+00:00
-- url     : https://prove2.me/theorems/602f5094-3bdb-45bb-955d-1fc994d63e91
-- title:
--   Lemma A.1 — triangular exchange for forests
-- statement:
--   **Lemma A.1 (Triangular exchange for forests).** Let $F$ be a forest. For an edge $e$ whose ends are connected in $F$, let $P_F(e)$ denote the path between them. Let $(e_1,f_1),\dots,(e_t,f_t)$ be pairs with $e_i\notin F$, $f_i\in F$ and $f_i\in P_F(e_i)$ for every $i$, and assume that $f_j\notin P_F(e_i)$ for every $i<j$. Then
--
--   $$F+\{e_1,\dots,e_t\}-\{f_1,\dots,f_t\}$$
--
--   is again a forest. It is the tool for executing several forest swaps at once.
--
--   **Formalization Note** "$f$ lies on $P_F(e)$" is expressed as: the ends of $e$ are connected in $F$ but not in $F-f$, which characterizes the unique path in a forest.
--
--   Differences from the source: none.
-- source:
--   Zhaienhe Zhou, STOC 2027 submission #1416 (October 2026), App. A, p.33, Lemma A.1

import Mathlib
import Definitions.Def_MinCostArbPacking_Main_Graph
set_option autoImplicit false

namespace MinCostArbPacking.Main

/-- Lemma A.1 (Triangular exchange for forests), p.33: let `F` be a forest and `(e₁, f₁), …,
(e_t, f_t)` pairs with `eᵢ ∉ F`, `fᵢ ∈ F`, `fᵢ ∈ P_F(eᵢ)` for every `i`, and `f_j ∉ P_F(eᵢ)` for every
`i < j`. Then `F + {e₁, …, e_t} - {f₁, …, f_t}` is again a forest. -/
theorem lemma_A_1 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : Digraph V E) (F : Finset E) (hF : G.IsForest F) (t : ℕ)
    (e f : Fin t → E) (hef : ∀ i, e i ∉ F ∧ G.OnPath F (e i) (f i))
    (hord : ∀ i j, i < j → ¬ G.OnPath F (e i) (f j)) :
    G.IsForest ((F \ Finset.univ.image f) ∪ Finset.univ.image e) := by sorry

end MinCostArbPacking.Main
