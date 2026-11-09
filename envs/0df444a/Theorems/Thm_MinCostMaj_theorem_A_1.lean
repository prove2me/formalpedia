-- Prove2me | Theorems.Thm_MinCostMaj_theorem_A_1
-- name    : MinCostMaj.theorem_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:20:30.585455+00:00
-- url     : https://prove2.me/theorems/d8b4a676-44ae-491e-90d6-8bf88d7a312d
-- title:
--   Theorem A.1 — the connected case: a proper subinstance, a blow-up, or a proper linked pattern
-- statement:
--   Let $I$ be a finite arc-consistent instance (opposite readings) with at least one potato of size at least two and with connected input (every two variables are joined by a pattern). Then at least one of the following holds:
--
--   1. there is an arc-consistent $I'\le I$ with $A^{I'}_u\subsetneq A^I_u$ for some $u$;
--   2. there are a variable $x$ and a pattern $p$ from $x$ to $x$ such that the relation "connected by $p$" on $A^I_x$ defines a blow-up of a grid of size $\ge2$, or a blow-up of a disjoint union of directed cycles at least one of which has length $\ge2$;
--   3. some pattern from $x$ to $y$ defines a proper linked relation in $A^I_x\times A^I_y$.
--
--   This is the core case analysis behind Theorem 4.1.
--
--   Differences from the source:
--   - reading: instances of CSP(A) on a variable set V → finite variable and value types (`Finite V`, `Finite D`) with the opposite-readings convention `IsSymm` as a hypothesis; reason: instances are finite inputs and §3 assumes R_vu holds the opposite readings of R_uv for every instance
--   - encoding: a pattern R_1,…,R_n along u = w_0,…,w_n = v → the start u and the list of steps (R_i, w_i); concatenation is list append; reason: same patterns
--   - encoding: defines a blow-up of a disjoint union of directed cycles, at least one of length ≥ 2 → nonempty blocks partitioning A^I_x, indexed by Fin m, with a related to b iff block(b) = σ(block(a)) for a permutation σ ≠ id; reason: a disjoint union of directed cycles is the functional graph of a permutation; its fixed points are the loops Z_1
-- source:
--   Kozik, Živný, Constant-factor approximation of MinCostCSP with a conservative majority polymorphism, arXiv:2607.10667 (held version, sha256 ec17e13c…), Theorem A.1, p.13 (PDF p.14)

import Mathlib
import Definitions.Def_MinCostMaj_BinInst
import Definitions.Def_MinCostMaj_Pattern
import Definitions.Def_MinCostMaj_BlowUp
import Definitions.Def_MinCostMaj_BinPol

namespace MinCostMaj

/-- **Theorem A.1**, p.13 (PDF p.14; proof pp.14–16).

Kozik, Živný, *Constant-factor approximation of MinCostCSP with a conservative majority
polymorphism*, arXiv:2607.10667, Theorem A.1, p.13: "Assume that I is binary, arc-consistent and has at least one potato of size
at least two. Moreover, assume that I has connected input. Then at least one of the following
holds:
1. there exists a proper (i.e., at least one A^{I′}_u ⊊ A^I_u) arc-consistent subinstance I′ ≤ I,
2. there is a variable x and a pattern p from x to x, such that the “connected by p” relation on
A^I_x defines a blow-up of a grid of size ≥ 2, or a blow-up of a disjoint union of directed cycles,
at least one of length ≥ 2,
3. there is a pattern defining a proper linked subrelation of a product of two potatoes."

**Formalization Note.** Finite instance with §3's opposite-readings convention; "connected input"
(p.12): every two variables are joined by a pattern. The "connected by p" relation on `A^I_x` is
`Connects a l b` for `a, b ∈ A^I_x`; blow-ups as in `IsBlowUpOfCycles`, `IsBlowUpOfGrid`. -/
theorem theorem_A_1 {V D : Type*} [Finite V] [Finite D] (I : BinInst V D) (hS : I.IsSymm)
    (hAC : I.IsArcConsistent) (h2 : ∃ u, 1 < (I.pot u).ncard) (hconn : I.ConnectedInput) :
    I.HasProperACSub ∨
    (∃ (x : V) (l : List (Set (D × D) × V)), IsPat I.rels x l x ∧
      (IsBlowUpOfGrid (I.pot x) (fun a b => Connects a l b) ∨
        IsBlowUpOfCycles (I.pot x) (fun a b => Connects a l b))) ∨
    (∃ (x y : V) (l : List (Set (D × D) × V)), IsPat I.rels x l y ∧
      IsProperRel (I.pot x) (I.pot y) (patRel I x y l) ∧
      IsLinked (I.pot x) (I.pot y) (patRel I x y l)) := by sorry

end MinCostMaj
