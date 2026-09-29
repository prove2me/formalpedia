-- Prove2me | Theorems.Thm_OPG1808_induced_subtournament_reachability_lifts
-- name    : OPG1808.induced_subtournament_reachability_lifts
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-24T06:07:18.357985+00:00
-- url     : https://prove2.me/theorems/22408fa8-40b9-41f4-b6ec-a960d38debc2
-- title:
--   Monochromatic reachability lifts from induced subtournaments
-- statement:
--   Monochromatic reachability lifts from induced subtournaments: if s reaches t by a directed path of color i whose vertices all lie in the vertex set C, then s monochromatically reaches t (in color i) in the whole tournament. This is the definitional wiring used to extend a monochromatic source of a source strong component to the whole tournament.
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

/-- M3: monochromatic reachability in an induced subtournament lifts to the
whole tournament. A monochromatic directed path whose vertices all lie in `C`
is a monochromatic directed path in `T`. -/
theorem induced_subtournament_reachability_lifts
    {V : Type} [Fintype V]
    (D : Digraph V) (color : ArcColoring V)
    (C : Finset V) (s t : V) (i : Fin 3)
    (h : Relation.ReflTransGen
      (fun x y : V => x ∈ C ∧ y ∈ C ∧ D.Adj x y ∧ color x y = i) s t) :
    MonochromaticallyReaches D color s t i := by sorry

end OPG1808
