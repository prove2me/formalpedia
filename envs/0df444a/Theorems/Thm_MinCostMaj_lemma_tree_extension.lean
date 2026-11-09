-- Prove2me | Theorems.Thm_MinCostMaj_lemma_tree_extension
-- name    : MinCostMaj.lemma_tree_extension
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:17:59.848972+00:00
-- url     : https://prove2.me/theorems/f8d528b1-7787-4b7f-ad1a-b738d1d06067
-- title:
--   Lemma "Tree extension and arc-consistency" — arc-consistent subinstances and realizable tree patterns
-- statement:
--   Let $K$ be a finite instance (opposite readings). The following are equivalent:
--
--   1. there is an arc-consistent (hence nonempty) $I\le K$;
--   2. every finite tree pattern in $K$ has a realization;
--   3. a universal covering pattern for $K$ has a realization.
--
--   Moreover, if $I\le K$ is arc-consistent, then for every finite tree pattern $t$ in $K$, every vertex $x$ of $t$ and every $a\in A^I_{\ell(x)}$ ($\ell(x)$ the variable label of $x$), there is a realization of $t$ in $I$ sending $x$ to $a$; the same holds for the universal covering pattern.
--
--   This lemma converts solvability of augmented covers into arc consistency of the level instances in the proof of Proposition 5.4.
--
--   Differences from the source:
--   - reading: instances of CSP(A) on a variable set V → finite variable and value types (`Finite V`, `Finite D`) with the opposite-readings convention `IsSymm` as a hypothesis; reason: instances are finite inputs and §3 assumes R_vu holds the opposite readings of R_uv for every instance
--   - reading: a universal covering pattern for K → the forest of walk trees of K, one tree per variable (`CoverVert`, `IsCoverRealization`); reason: every copy of x has, for each y and R ∈ R_xy, an edge labelled R to a copy of y; one tree per variable is needed to cover tree patterns in every connected component
--   - encoding: I arc-consistent and nonempty → I arc-consistent (all potatoes nonempty is part of arc consistency); reason: same condition
--   - encoding: finite tree pattern → a tree on Fin m with variable labels and a constraint for each oriented edge, opposite orientations carrying opposite readings; reason: same objects
-- source:
--   Kozik, Živný, Constant-factor approximation of MinCostCSP with a conservative majority polymorphism, arXiv:2607.10667 (held version, sha256 ec17e13c…), Lemma "Tree extension and arc-consistency", p.23 (PDF p.24)

import Mathlib
import Definitions.Def_MinCostMaj_BinInst
import Definitions.Def_MinCostMaj_TreePattern

namespace MinCostMaj

/-- **Lemma "Tree extension and arc-consistency"**, p.23 (PDF p.24).

Kozik, Živný, *Constant-factor approximation of MinCostCSP with a conservative majority
polymorphism*, arXiv:2607.10667, p.23: "Let K be a binary instance. The following are equivalent:
1. there exists I ≤ K such that I is arc-consistent and nonempty;
2. every finite tree pattern in K has a realization;
3. a universal covering pattern for K has a realization.
Moreover, if I ≤ K is arc-consistent and nonempty, then for every finite tree pattern t in K, every
vertex x of t, and every a ∈ A^I_{ℓ(x)} (where ℓ(x) is the variable-label of x), there is a
realization of t in I sending x to a. The same holds when t is a universal covering pattern for K."

**Formalization Note.** "Nonempty" (every potato nonempty) is part of arc consistency. Realizations
in `K` take values in `K`'s potatoes, realizations in `I` in `I`'s potatoes. The universal
covering pattern is the forest of walk trees (`CoverVert`, `IsCoverRealization`). Finite instance
with §3's opposite-readings convention. -/
theorem lemma_tree_extension {V D : Type*} [Finite V] [Finite D] (K : BinInst V D)
    (hS : K.IsSymm) :
    [∃ I : BinInst V D, I.Le K ∧ I.IsArcConsistent,
      ∀ t : FinTreePattern K, ∃ β, t.IsRealization K.pot β,
      ∃ β, IsCoverRealization K K.pot β].TFAE ∧
    ∀ I : BinInst V D, I.Le K → I.IsArcConsistent →
      (∀ (t : FinTreePattern K) (x : Fin t.m), ∀ a ∈ I.pot (t.lab x),
        ∃ β, t.IsRealization I.pot β ∧ β x = a) ∧
      (∀ v : CoverVert K, ∀ a ∈ I.pot (walkEnd v.1.1 v.1.2),
        ∃ β, IsCoverRealization K I.pot β ∧ β v = a) := by sorry

end MinCostMaj
