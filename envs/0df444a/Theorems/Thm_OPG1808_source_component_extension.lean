-- Prove2me | Theorems.Thm_OPG1808_source_component_extension
-- name    : OPG1808.source_component_extension
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-24T06:08:02.910991+00:00
-- url     : https://prove2.me/theorems/2605c940-c818-4c3c-a5d4-ab620807945f
-- title:
--   Monochromatic source of a dominating vertex set extends to the whole tournament
-- statement:
--   Let T be a finite tournament with arcs colored in three colors, and let C be a nonempty set of vertices such that every arc between C and the complement of C points out of C. If a vertex s in C reaches every vertex of C by directed monochromatic paths that stay inside C (the color may depend on the target), then s is a monochromatic source of the whole tournament: every vertex outside C is reached in one step, and every vertex inside C by the given paths.
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

/-- M1: a monochromatic source of a dominating vertex set extends to the whole
tournament. If every arc between `C` and its complement points out of `C`,
and `s ∈ C` reaches every vertex of `C` by monochromatic paths staying inside
`C`, then `s` reaches every vertex of the whole tournament monochromatically. -/
theorem source_component_extension
    {V : Type} [Fintype V]
    (D : Digraph V) (color : ArcColoring V)
    (C : Finset V) (s : V)
    (hsC : s ∈ C)
    (hdom : ∀ x ∈ C, ∀ y : V, y ∉ C → D.Adj x y)
    (hsrc : ∀ t ∈ C, ∃ i : Fin 3,
      Relation.ReflTransGen (fun x y : V => x ∈ C ∧ y ∈ C ∧ D.Adj x y ∧ color x y = i) s t) :
    IsMonochromaticSource D color s := by sorry

end OPG1808
