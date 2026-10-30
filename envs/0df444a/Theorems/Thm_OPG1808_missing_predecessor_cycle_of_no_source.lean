-- Prove2me | Theorems.Thm_OPG1808_missing_predecessor_cycle_of_no_source
-- name    : OPG1808.missing_predecessor_cycle_of_no_source
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-29T23:53:33.993069+00:00
-- url     : https://prove2.me/theorems/761b9151-9091-4494-9871-dd94b246b259
-- title:
--   A tournament without a monochromatic source contains an obstruction cycle
-- statement:
--   Let $V$ be a nonempty finite vertex set, let $D$ be a tournament on $V$, and color its arcs with three colors. Say that $x$ reaches $y$ monochromatically when there is a directed path from $x$ to $y$ all of whose arcs have one color; the path color may depend on the ordered pair. If no vertex reaches every vertex monochromatically, there are an integer $m$ and distinct vertices $v_0,\ldots,v_{m-1}$ such that
--
--   $$
--   3\le m\le |V|,\qquad
--   v_i\to v_{i+1},\qquad
--   v_{i+1}\not\leadsto v_i\text{ monochromatically}
--   \quad(i\in\mathbb Z/m\mathbb Z).
--   $$
--
--   The non-reachability is in the whole tournament. This extracts a simple directed obstruction cycle for finite counterexample searches. The cycle need not span all vertices. No restriction on rainbow triangles and no minimal-counterexample assumption is required.
-- source:
--   Georgakopoulos--Sprüssel, On 3-coloured tournaments, https://arxiv.org/abs/0904.1967v2, p. 2, opening paragraph of the proof of Lemma 2.1. This is the auxiliary simple-cycle extraction used there, isolated before the minimality argument; not the full Hamilton-cycle conclusion of Lemma 2.1.

import Definitions.Def_opg1808_colored_tournaments
import Mathlib.Logic.Equiv.Fin.Rotate

open OPG1808
universe u

theorem OPG1808.missing_predecessor_cycle_of_no_source{V : Type u} [Fintype V] [Nonempty V]
    (D : Digraph V) (color : ArcColoring V)
    (ht : IsTournament D) (hnosource : ¬∃ s : V, IsMonochromaticSource D color s) :
    ∃ m : ℕ, 3 ≤ m ∧ m ≤ Fintype.card V ∧
      ∃ e : Fin m → V, Function.Injective e ∧
        ∀ i : Fin m, D (e i) (e (finRotate m i)) ∧
          ¬MonochromaticallyReaches D color (e (finRotate m i)) (e i) := by sorry
