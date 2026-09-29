-- Prove2me | Theorems.Thm_OPG1808_landau_king_theorem
-- name    : OPG1808.landau_king_theorem
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-24T06:07:26.724771+00:00
-- url     : https://prove2.me/theorems/9e0d7bd0-7ca0-4696-ab78-2fba2acb6ec5
-- title:
--   Landau's king theorem: every finite tournament has a king vertex
-- statement:
--   Landau's king theorem: every nonempty finite tournament has a king vertex — a vertex v such that every other vertex u is either equal to v, an out-neighbor of v, or reachable from v by a directed path of length two. Classical standalone scaffolding for tournament reachability arguments.
-- source:
--   Open Problem Garden, Monochromatic reachability versus rainbow triangles, https://www.openproblemgarden.org/op/monochromatic_reachability_vs_rainbow_triangles; structural lemma toward OPG-1808 (Sands--Sauer--Woodrow, JCTB 33 (1982), 271-275)

import Mathlib

namespace OPG1808

/-- A 3-coloring of the ordered vertex pairs (arcs). -/
abbrev ArcColoring (V : Type) : Type := V → V → Fin 3

/-- A digraph is a tournament: no loops, and for every two distinct vertices
exactly one of the two possible arcs is present. -/
def IsTournament {V : Type} (D : Digraph V) : Prop :=
  (∀ v : V, ¬ D.Adj v v) ∧
    ∀ a b : V, a ≠ b → (D.Adj a b ∨ D.Adj b a) ∧ ¬ (D.Adj a b ∧ D.Adj b a)

/-- A rainbow directed triangle: three distinct vertices a, b, c with arcs
a → b → c → a whose three colors are pairwise distinct. -/
def HasRainbowDirectedTriangle {V : Type} (D : Digraph V) (color : ArcColoring V) : Prop :=
  ∃ a b c : V, a ≠ b ∧ b ≠ c ∧ c ≠ a ∧ D.Adj a b ∧ D.Adj b c ∧ D.Adj c a ∧
    color a b ≠ color b c ∧ color b c ≠ color c a ∧ color c a ≠ color a b

/-- Monochromatic reachability: a directed path of zero or more arcs, all of one color. -/
def MonochromaticallyReaches {V : Type} (D : Digraph V) (color : ArcColoring V)
    (s t : V) (i : Fin 3) : Prop :=
  Relation.ReflTransGen (fun x y : V => D.Adj x y ∧ color x y = i) s t

/-- A monochromatic source: every vertex is monochromatically reachable from `s`
(the color may be chosen separately for each target). -/
def IsMonochromaticSource {V : Type} (D : Digraph V) (color : ArcColoring V) (s : V) : Prop :=
  ∀ t : V, ∃ i : Fin 3, MonochromaticallyReaches D color s t i

end OPG1808

namespace OPG1808

/-- M4 (Landau's king theorem): every nonempty finite tournament has a king
vertex, i.e. a vertex reaching every other vertex by a directed path of length
at most two. -/
theorem landau_king_theorem
    {V : Type} [Fintype V] [Nonempty V]
    (D : Digraph V)
    (ht : IsTournament D) :
    ∃ v : V, ∀ u : V, u = v ∨ D.Adj v u ∨ ∃ w : V, D.Adj v w ∧ D.Adj w u := by sorry

end OPG1808
