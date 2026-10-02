-- Prove2me | Theorems.Thm_OPG1808_minimal_counterexample_strongly_connected
-- name    : OPG1808.minimal_counterexample_strongly_connected
-- status  : Disproved
-- author  : @junyihjy
-- created : 2026-09-24T06:07:13.5392+00:00
-- url     : https://prove2.me/theorems/13654e1a-0f26-4641-a61a-9414fdc8b96c
-- title:
--   A minimal counterexample to the rainbow-triangle dichotomy is strongly connected
-- statement:
--   A minimal counterexample to the OPG-1808 dichotomy is strongly connected. More precisely: let T be a finite 3-arc-colored tournament with no rainbow directed triangle, and assume every proper nonempty vertex set C with all arcs to its complement pointing outward already contains a vertex that monochromatically reaches all of C inside C. Then no such proper nonempty C exists — i.e. T has no nontrivial source strong component.
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

/-- M2: a minimal counterexample is strongly connected. If `T` has no rainbow
directed triangle and every proper nonempty dominated vertex set already
contains a monochromatic source of its induced subtournament, then `T` admits
no nontrivial dominating set (i.e. no proper nonempty `C` with all
`C`-to-complement arcs pointing outward). -/
theorem minimal_counterexample_strongly_connected
    {V : Type} [Fintype V]
    (D : Digraph V) (color : ArcColoring V)
    (hnorainbow : ¬ HasRainbowDirectedTriangle D color)
    (hmin : ∀ C : Finset V, C.Nonempty → C ≠ Finset.univ →
      (∀ x ∈ C, ∀ y : V, y ∉ C → D.Adj x y) →
      ∃ s ∈ C, ∀ t ∈ C, ∃ i : Fin 3,
        Relation.ReflTransGen
          (fun x y : V => x ∈ C ∧ y ∈ C ∧ D.Adj x y ∧ color x y = i) s t) :
    ¬ ∃ C : Finset V, C.Nonempty ∧ C ≠ Finset.univ ∧
      ∀ x ∈ C, ∀ y : V, y ∉ C → D.Adj x y := by sorry

end OPG1808
