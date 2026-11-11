-- Prove2me | Theorems.Thm_HomIndGHW_RCR_theorem_1_2
-- name    : HomIndGHW.RCR.theorem_1_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:02:25.991308+00:00
-- url     : https://prove2.me/theorems/963f0dc5-cf18-45a5-80d1-565d7147d3ee
-- title:
--   Theorem 1.2 — k-RCR distinguishes A and B iff some connected structure of generalised hypertree width ≤ k has different homomorphism counts into them
-- statement:
--   Let $\sigma$ be any finite relational signature with positive arities and $k\ge1$. For all finite $\sigma$-structures $\mathcal A,\mathcal B$ without isolated elements, the following are equivalent:
--
--   1. $k$-RCR distinguishes $\mathcal A$ and $\mathcal B$ (that is, $\mathcal A\not\equiv_{k\text{-RCR}}\mathcal B$, Definition 1.3);
--   2. there is a connected finite $\sigma$-structure $\mathcal C$ without isolated elements that admits a generalised hypertree decomposition of width at most $k$ such that
--   $$\#\mathrm{Hom}(\mathcal C,\mathcal A)\neq\#\mathrm{Hom}(\mathcal C,\mathcal B).$$
--
--   This is the paper's main theorem: the relational $k$-dimensional colour refinement $k$-RCR has exactly the distinguishing power of homomorphism counts from structures of generalised hypertree width at most $k$, extending Dvořák's and Dell–Grohe–Rattan's characterisation of colour refinement (and Scheidt–Schweikardt's case $k=1$) to every $k$.
--
--   Differences from the source:
--
--   - encoding: σ-structures, implicitly finite (#Hom is "the cardinality of a finite set", p. 14) → domains are types with [Fintype _]; relations are sets of tuples Fin (ar R) → V, hence finite; reason: finite domains are the paper's setting; a tuple of length ar(R) is a function on Fin (ar R)
--   - reading: σ-structures, which by Remark 2.1 (p. 14) and Remark 3.1 (p. 18) never have isolated elements → hypotheses A.NoIsolated, B.NoIsolated on every σ-structure of the statement; reason: the paper's standing assumption, stated once for the whole paper; the theorem's sentence relies on it
--   - encoding: a finite relational signature σ with positive arities → Sig (a finite type of symbols, arities with ar_pos); reason: same objects; the symbols are an arbitrary finite type
--   - encoding: ≡_{k-RCR} via the stable colouring κ_∞ and E^A_k(c) = E^B_k(c) for all stable colours c (Definition 1.3) → RCREquiv: for every round i and every canonical round-i colour c, the numbers of flat tuples of A and of B with κ_i = c agree; reason: colours are canonical values comparable across structures; equal round-(i+1) histograms give equal round-i histograms, and after both colourings are stable equal histograms propagate to every later round, so the all-rounds form is the stable-colour comparison
--   - encoding: flat tuples and pro-tuples (α; t̄_1, …, t̄_m) with 1-based positions → flat tuples are List V; a pro-tuple is the pair (α, t̄_1 + ⋯ + t̄_m) as in §4; stp keeps the 1-based indices; reason: the arities in α recover the t̄_i, so the pair determines the pro-tuple
--   - encoding: a GHD (T, B, λ) with T a tree, λ(v) a sequence of coloured tuples, width max |λ(v)| → GHD on a finite node type with T.IsTree, lam v : List (CT A), WidthLe k = ∀ v, (lam v).length ≤ k; condition (2) as Preconnected of the induced subgraph; reason: same objects; Preconnected lets an element in no bag impose nothing, and for structures without isolated elements every element lies in a bag by condition (1)
--   - encoding: C connected (not defined in the paper) → (gaifman C).Connected (Mathlib: connected and nonempty); reason: the standard reading; the empty structure has exactly one homomorphism into every structure and never separates two structures
--   - encoding: "there is a σ-structure C" → ∃ n, ∃ C : Structure σ (Fin n); reason: every finite structure is isomorphic to one on Fin n, and hom counts are invariant under isomorphism
--   - reading: "a connected σ-structure C" (Remark 2.1) → C.NoIsolated in the existential; reason: the standing assumption covers C; without it the statement fails (one isolated point vs two: k-RCR sees no tuples, a single point has 1 ≠ 2 homomorphisms)
-- source:
--   Aivasiliotis, Chen, Göbel, Lanzinger, Roth, Schneider, Homomorphism Indistinguishability Beyond Graphs, consolidated manuscript (catalogued as arXiv:2607.07934; sha256 671ba611…), p. 4, Theorem 1.2

import Mathlib
import Definitions.Def_HomIndGHW_RCR_Structures
import Definitions.Def_HomIndGHW_RCR_GHD
import Definitions.Def_HomIndGHW_RCR_Refinement

open Classical HomIndGHW.RCR.Structure

namespace HomIndGHW.RCR

/-- Theorem 1.2 (Main Theorem, p. 4): for every finite signature `σ` with positive arities, every
`k ≥ 1` and all finite `σ`-structures `A`, `B` without isolated elements, k-RCR distinguishes `A`
and `B` iff there is a connected `σ`-structure `C` (finite, without isolated elements) that admits
a generalised hypertree decomposition of width at most `k` with `#Hom(C, A) ≠ #Hom(C, B)`. -/
theorem theorem_1_2 {σ : Sig} (k : ℕ) (hk : 1 ≤ k) {V W : Type*} [Fintype V] [Fintype W]
    (A : Structure σ V) (B : Structure σ W) (hA : A.NoIsolated) (hB : B.NoIsolated) :
    RCRDistinguishes k A B ↔
      ∃ (n : ℕ) (C : Structure σ (Fin n)), C.NoIsolated ∧ C.Connected ∧ AdmitsGHD C k ∧
        homCount C A ≠ homCount C B := by sorry

end HomIndGHW.RCR
