-- Prove2me | Theorems.Thm_MinCostMaj_theorem_4_1
-- name    : MinCostMaj.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:17:38.900206+00:00
-- url     : https://prove2.me/theorems/f1199ade-66fd-4599-b6a3-af3dcaa68787
-- title:
--   Theorem 4.1 — a proper subinstance, a cycle or grid blow-up, or $R_{00}$/$R_{11}$ patterns
-- statement:
--   Let $I$ be a finite arc-consistent instance (opposite readings) with at least one potato with at least two elements. Then:
--
--   1. there is an arc-consistent $I'\le I$ with $A^{I'}_u\subsetneq A^I_u$ for some $u$; or
--   2. there are a variable $x$ and a pattern $p$ from $x$ to $x$ such that the relation "connected by $p$" on $A^I_x$ defines a blow-up of a disjoint union of directed cycles, at least one of length $\ge2$, or a blow-up of a grid of size $\ge2$; or
--   3. there are a variable $x$, two distinct values $0,1\in A^I_x$ and patterns $p_{00},p_{11}$ from $x$ to $x$ such that, after restricting the potatoes along each pattern to suitable two-element subsets (equal to $\{0,1\}$ at both ends), $p_{00}$ defines $R_{00}$ or $\ne$, and $p_{11}$ defines $R_{11}$ or $\ne$, where $R_{ij}=\{0,1\}^2\setminus\{(i,j)\}$.
--
--   No polymorphism is assumed. Each outcome yields gadgets for the reduction from $\mathrm{cUG}(k)$ in §4.1.
--
--   Differences from the source:
--   - reading: instances of CSP(A) on a variable set V → finite variable and value types (`Finite V`, `Finite D`) with the opposite-readings convention `IsSymm` as a hypothesis; reason: instances are finite inputs and §3 assumes R_vu holds the opposite readings of R_uv for every instance
--   - encoding: a pattern R_1,…,R_n along u = w_0,…,w_n = v → the start u and the list of steps (R_i, w_i); concatenation is list append; reason: same patterns
--   - encoding: defines a blow-up of a disjoint union of directed cycles, at least one of length ≥ 2 → nonempty blocks partitioning A^I_x, indexed by Fin m, with a related to b iff block(b) = σ(block(a)) for a permutation σ ≠ id; reason: a disjoint union of directed cycles is the functional graph of a permutation; its fixed points are the loops Z_1
--   - reading: after restricting intermediate potatoes to suitable two-element subsets, p00 defines R00 or ≠ → a two-element subset of the potato at every position of the pattern, equal to {0,1} at both ends, and the relation connected through these subsets equals R00 or ≠ on {0,1}; reason: R00 and ≠ are relations on {0,1}, so the end positions are restricted to {0,1}
-- source:
--   Kozik, Živný, Constant-factor approximation of MinCostCSP with a conservative majority polymorphism, arXiv:2607.10667 (held version, sha256 ec17e13c…), Theorem 4.1, pp.7–8 (PDF pp.8–9); restated p.12 (PDF p.13)

import Mathlib
import Definitions.Def_MinCostMaj_BinInst
import Definitions.Def_MinCostMaj_Pattern
import Definitions.Def_MinCostMaj_BlowUp

namespace MinCostMaj

/-- **Theorem 4.1**, pp.7–8 (PDF pp.8–9; restated p.12; proof Appendix A).

Kozik, Živný, *Constant-factor approximation of MinCostCSP with a conservative majority
polymorphism*, arXiv:2607.10667, Theorem 4.1, pp.7–8: "Assume that I is binary, arc-consistent and has at least one potato with
at least two elements. Then:
1. there exists a proper (i.e., at least one A^{I′}_u ⊊ A^I_u) arc-consistent subinstance I′ ≤ I, or
2. there is a variable x and a pattern p from x to x, such that the “connected by p” relation on
A^I_x defines a blow-up of a disjoint union of directed cycles, at least one of length ≥ 2, or a
blow-up of a grid of size ≥ 2, or
3. there exists a variable x, two elements 0, 1 ∈ A^I_x, and patterns p00 and p11 from x to x such
that, after restricting intermediate potatoes to suitable two-element subsets, p00 defines R00 or ≠
and p11 defines R11 or ≠."

**Formalization Note.** Finite instance with §3's opposite-readings convention; no polymorphism is
assumed. Item 3: the two values are `e₀ ≠ e₁`, `R₀₀ = {e₀,e₁}² ∖ {(e₀,e₀)}`,
`R₁₁ = {e₀,e₁}² ∖ {(e₁,e₁)}`, `≠ = {(e₀,e₁),(e₁,e₀)}`; the restriction picks a two-element subset
of the potato at every position of the pattern, `{e₀, e₁}` at both ends (`DefinesRestricted`). -/
theorem theorem_4_1 {V D : Type*} [Finite V] [Finite D] (I : BinInst V D) (hS : I.IsSymm)
    (hAC : I.IsArcConsistent) (h2 : ∃ u, 1 < (I.pot u).ncard) :
    I.HasProperACSub ∨
    (∃ (x : V) (l : List (Set (D × D) × V)), IsPat I.rels x l x ∧
      (IsBlowUpOfCycles (I.pot x) (fun a b => Connects a l b) ∨
        IsBlowUpOfGrid (I.pot x) (fun a b => Connects a l b))) ∨
    (∃ (x : V) (e₀ e₁ : D) (l₀₀ l₁₁ : List (Set (D × D) × V)),
      e₀ ∈ I.pot x ∧ e₁ ∈ I.pot x ∧ e₀ ≠ e₁ ∧ IsPat I.rels x l₀₀ x ∧ IsPat I.rels x l₁₁ x ∧
      (DefinesRestricted I x e₀ e₁ l₀₀ (R00 e₀ e₁) ∨ DefinesRestricted I x e₀ e₁ l₀₀ (Ne2 e₀ e₁)) ∧
      (DefinesRestricted I x e₀ e₁ l₁₁ (R11 e₀ e₁) ∨
        DefinesRestricted I x e₀ e₁ l₁₁ (Ne2 e₀ e₁))) := by sorry

end MinCostMaj
