-- Prove2me | Theorems.Thm_MinCostMaj_lemma_saturation_cycle_blowups
-- name    : MinCostMaj.lemma_saturation_cycle_blowups
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:15:22.343242+00:00
-- url     : https://prove2.me/theorems/fb5a79b9-4e33-42ce-9016-95e0fce9f9ee
-- title:
--   Lemma "Saturation on cycle blow-ups" — $(k+1)p$ keeps the cycle in $I$ and is full on $C$ in $J$
-- statement:
--   Let $(I,J)$ be an ac-leq-cycle pair of finite instances (opposite readings), $x$ a variable and $p$ a pattern from $x$ to $x$. Let $k\ge2$ and let $B_0,\dots,B_{k-1}$ be nonempty, pairwise disjoint subsets of $A^I_x$ with $C=B_0\cup\dots\cup B_{k-1}$, such that in $I$ the pattern $p$ connects each $a\in B_i$ to exactly the elements of $B_{i+1\bmod k}$ among $A^I_x$. Let $q=(k+1)p$. Then
--
--   1. in $I$, $q$ defines the same relation on $C$ as $p$;
--   2. in $J$, $q$ connects every element of $C$ to every element of $C$.
--
--   This makes every pair of endpoint values realizable at cost $0$ inside $I$ or at positive cost through $J$, which is the gadget of the reduction from $\mathrm{cUG}(k)$.
--
--   Differences from the source:
--   - reading: instances of CSP(A) on a variable set V → finite variable and value types (`Finite V`, `Finite D`) with the opposite-readings convention `IsSymm` as a hypothesis; reason: instances are finite inputs and §3 assumes R_vu holds the opposite readings of R_uv for every instance
--   - encoding: a pattern R_1,…,R_n along u = w_0,…,w_n = v → the start u and the list of steps (R_i, w_i); concatenation is list append; reason: same patterns
--   - reading: C = B_0 ∪ ··· ∪ B_{k−1} ⊆ A^I_x the vertices of a blow-up of a directed cycle (in the blow-up of a union of directed cycles of Item 2) → nonempty pairwise disjoint B_i ⊆ A^I_x such that from a ∈ B_i the pattern reaches, inside A^I_x, exactly B_{i+1 mod k}; reason: C is one cycle of Item 2's blow-up, so p connects elements of C only to elements of C
--   - encoding: the pattern p in I and in J → a pattern of J, read in I with values restricted to the potatoes of I; reason: the constraints of I are those of J restricted to the potatoes of I, so the patterns of I are exactly these readings
-- source:
--   Kozik, Živný, Constant-factor approximation of MinCostCSP with a conservative majority polymorphism, arXiv:2607.10667 (held version, sha256 ec17e13c…), Lemma "Saturation on cycle blow-ups", p.9, with its setting on p.8 (PDF pp.9–10)

import Mathlib
import Definitions.Def_MinCostMaj_BinInst
import Definitions.Def_MinCostMaj_Pattern

namespace MinCostMaj

/-- **Lemma "Saturation on cycle blow-ups"**, p.9 (PDF p.10).

Kozik, Živný, *Constant-factor approximation of MinCostCSP with a conservative majority
polymorphism*, arXiv:2607.10667, p.8: "Let x be the variable, let p be the pattern, and let C = B0 ∪ · · · ∪ Bk−1 ⊆ A^I_x be
the vertices of a blow-up of a directed cycle, with k ≥ 2. Thus, in I, the pattern p connects
precisely the pairs Bi × Bi+1 (for every i with addition modulo k), and no other pairs inside C."
Lemma, p.9: "Let q = (k + 1)p be the concatenation of k + 1 copies of p. Then, in I, the pattern q
defines the same relation on C as p, and, in J, the pattern q connects every element of C to every
element of C."

`(I, J)` is an ac-leq-cycle pair; `p` (the list `l`) is a closed pattern at `x` of `J`, read in
`I` with values in the potatoes of `I` (`ConnectsIn I.pot`) and in `J` with values in those of
`J`. The blocks `B 0, …, B (k−1)` are nonempty, pairwise disjoint subsets of `A^I_x`, and from
`a ∈ Bᵢ` the pattern reaches, inside `A^I_x`, exactly `B_{i+1 mod k}` (`finRotate k i`).

**Formalization Note.** "The vertices of a blow-up of a directed cycle" in the blow-up of a union of
cycles of Item 2: `C` is a whole cycle component, so from `C` the pattern only reaches `C`. Every
pattern of `I` is a pattern of `J` read in `I` (`R^I = {R ∩ (A^I × A^I)}`). Finite instances with
§3's opposite-readings convention. -/
theorem lemma_saturation_cycle_blowups {V D : Type*} [Finite V] [Finite D] (I J : BinInst V D)
    (hSI : I.IsSymm) (hSJ : J.IsSymm) (hpair : I.AcLeqCycle J) (x : V)
    (l : List (Set (D × D) × V)) (hl : IsPat J.rels x l x) (k : ℕ) (hk : 2 ≤ k)
    (B : Fin k → Set D) (hBne : ∀ i, (B i).Nonempty) (hBsub : ∀ i, B i ⊆ I.pot x)
    (hBdisj : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hcyc : ∀ i, ∀ a ∈ B i, ∀ b ∈ I.pot x, (ConnectsIn I.pot a l b ↔ b ∈ B (finRotate k i))) :
    (∀ a ∈ ⋃ i, B i, ∀ b ∈ ⋃ i, B i,
      (ConnectsIn I.pot a (repPat (k + 1) l) b ↔ ConnectsIn I.pot a l b)) ∧
    (∀ a ∈ ⋃ i, B i, ∀ b ∈ ⋃ i, B i, ConnectsIn J.pot a (repPat (k + 1) l) b) := by sorry

end MinCostMaj
