-- Prove2me | Theorems.Thm_FourColorLinear_lemma_9
-- name    : FourColorLinear.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:54:38.522967+00:00
-- url     : https://prove2.me/theorems/f66b5e4b-d8b9-4eda-bfe9-675c28767ef6
-- title:
--   Lemma 9 — encoding a plane graph with marked hole walks in $O(|H|)$ bits
-- statement:
--   For each $d$ and each bound $h$ on the number of holes per region, there are a constant $C$ and a code on plane graphs $H$ with marked hole information for $R_0,\dots,R_d$, of length at most $C(|H|+1)$ bits, such that two marked plane graphs have the same code exactly when a rotation-preserving isomorphism respects all marks.
--
--   So the code determines $H$ with its hole walks and their enumeration. This is what lets boundary structures of regions of size $\Theta(\log^2 n)$ be tabulated in Section 2.
--
--   Differences from the source:
--   - reading: "we can encode H using O(|H|) bits so that … we can identify the hole walks of Rj in H" → a code of the unlabelled marked plane graph, injective up to a rotation-preserving isomorphism respecting marks; reason: labelled planar graphs need Ω(n log n) bits; p.12 says the code gives "enumerations of the vertices and edges"
--   - encoding: O(|H|) bits → C·(|H| + 1) bits, C depending on d and h; reason: so that the empty H is covered; p.13 has O(1) children and a constant number of holes
-- source:
--   Inoue, Kawarabayashi, Miyashita, Mohar, Thomassen, Thorup, Four-Coloring Planar Graphs in Linear Time, arXiv:2610.39753 (held version, sha256 4dce39c5…), Lemma 9, p.13

import Mathlib
import Definitions.Def_FourColorLinear_MarkedPlane

namespace FourColorLinear

/-- Lemma 9 of arXiv:2610.39753 (held version, sha256 4dce39c5…), p.13: "For a region R0 with children R1, …, Rd, suppose we have a plane
graph H containing ⋃_{j=0}^d ∂Rj. Then we can encode H using O(|H|) bits so that, for each j = 0, …, d,
we can identify the hole walks of Rj in H."

**Formalization Note** The code is of the unlabelled marked plane graph: labelled planar graphs need
`Ω(n log n)` bits, and p.12 says the code gives the "enumerations of the vertices and edges". Two
instances get one code exactly when a rotation-preserving isomorphism respects all hole information.
The constant depends on `d` and on the bound `h` on holes. The statement makes no reference to the
codes cited by the proof. -/
theorem lemma_9 (d h : ℕ) :
    ∃ (C : ℕ) (code : MarkedPlane d h → List Bool),
      (∀ x, (code x).length ≤ C * (x.n + 1)) ∧
      ∀ x y, code x = code y ↔ MarkedPlane.Iso x y := by sorry

end FourColorLinear
