-- Prove2me | Theorems.Thm_OPG37271_exists_five_cycle_safe_edge_color
-- name    : OPG37271.exists_five_cycle_safe_edge_color
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T06:01:09.155722+00:00
-- url     : https://prove2.me/theorems/ea172e0a-73b2-4e96-a82e-12f926bf8fd3
-- title:
--   Safe edge and borrowed color selection on a 5-cycle (Cases 1 & 2)
-- statement:
--   Let the vertices of a $5$-cycle $C_5$ carry optional colors $f : \mathrm{Fin}\,5 \to \mathrm{Option}(\mathrm{Fin}\,4)$ such that adjacent vertices never carry the same color, and let $X$ be a list of at most two vertex-color conflict pairs $(v_x, c_x) \in \mathrm{Fin}\,5 \times \mathrm{Fin}\,4$. Then there exists an edge $e = (e, e+1)$ of $C_5$ and a color $\mathrm{col} \in \mathrm{Fin}\,4$ such that no vertex $u \ne e + 3$ of $C_5$ carries $\mathrm{col}$, and no conflict pair $(v_x, c_x) \in X$ with $v_x \in \{e, e+1\}$ has $c_x = \mathrm{col}$.
-- source:
--   Dvořák, Mohar, and Šámal, Star chromatic index, J. Graph Theory 72 (2013), 313–326 (arXiv:1011.3376), Section 4, proof of Theorem 4.1(a) (5-cycle Cases 1 and 2).

import Mathlib.Data.Fintype.Card

namespace OPG37271

theorem exists_five_cycle_safe_edge_color
    (f : Fin 5 → Option (Fin 4))
    (hadj : ∀ i : Fin 5, f i ≠ none → f i ≠ f (i + 1))
    (X : List (Fin 5 × Fin 4))
    (hX : X.length ≤ 2) :
    ∃ (e : Fin 5) (col : Fin 4),
      (∀ u : Fin 5, u ≠ e + 3 → f u ≠ some col) ∧
      (∀ p ∈ X, (p.1 = e ∨ p.1 = e + 1) → p.2 ≠ col) := by sorry
end OPG37271
