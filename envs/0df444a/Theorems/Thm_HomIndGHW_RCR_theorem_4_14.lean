-- Prove2me | Theorems.Thm_HomIndGHW_RCR_theorem_4_14
-- name    : HomIndGHW.RCR.theorem_4_14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:02:42.034291+00:00
-- url     : https://prove2.me/theorems/245fd1f5-cc1d-4f2c-9f9b-f3ab5e8e3227
-- title:
--   Theorem 4.14 (= Theorem 1.8) — k-RCR, ≡_c, ≡⁺_c and k-proRCR distinguish the same pairs
-- statement:
--   Let $k\ge1$, fix $\preceq_\sigma$, and let $\mathcal A,\mathcal B$ be finite $\sigma$-structures with disjoint domains (without isolated elements). A coarsest robust equivalence relation $\equiv_c$ on $T_k(\mathcal A)\cup T_k(\mathcal B)$ exists, and for every such $\equiv_c$ the following are equivalent:
--
--   1. $k$-RCR distinguishes $\mathcal A,\mathcal B$;
--   2. $\equiv_c$ distinguishes $\mathcal A,\mathcal B$;
--   3. $\equiv^+_c=\mathfrak E(\equiv_c)$ distinguishes $\mathcal A,\mathcal B$;
--   4. $k$-proRCR distinguishes $\mathcal A,\mathcal B$.
--
--   In particular $\mathcal A\equiv_{k\text{-RCR}}\mathcal B\iff\mathcal A\equiv_{k\text{-proRCR}}\mathcal B$ (Theorem 1.8).
--
--   Differences from the source:
--
--   - encoding: σ-structures, implicitly finite (#Hom is "the cardinality of a finite set", p. 14) → domains are types with [Fintype _]; relations are sets of tuples Fin (ar R) → V, hence finite; reason: finite domains are the paper's setting; a tuple of length ar(R) is a function on Fin (ar R)
--   - reading: σ-structures, which by Remark 2.1 (p. 14) and Remark 3.1 (p. 18) never have isolated elements → hypotheses A.NoIsolated, B.NoIsolated on every σ-structure of the statement; reason: the paper's standing assumption, stated once for the whole paper; the theorem's sentence relies on it
--   - encoding: a finite relational signature σ with positive arities and a fixed total order ⪯σ on its symbols → Sig (a finite type of symbols with ar_pos) and a [LinearOrder σ.Sym] binder; reason: the paper fixes an arbitrary total order (p. 6, p. 18); quantifying over every order covers each choice
--   - encoding: A, B "with disjoint domains", relations on T_k(A) ∪ T_k(B) (resp. MCT_k(A) ∪ MCT_k(B)) → domains V, W and the sum types FT A B k = T_k(A) ⊕ T_k(B), FP A B k = MCT_k(A) ⊕ MCT_k(B); equivalence relations are Setoids, ⊆ is ≤; reason: a disjoint union is a sum type; disjointness is automatic
--   - encoding: ≡_{k-RCR} via the stable colouring κ_∞ and E^A_k(c) = E^B_k(c) for all stable colours c (Definition 1.3) → RCREquiv: for every round i and every canonical round-i colour c, the numbers of flat tuples of A and of B with κ_i = c agree; reason: colours are canonical values comparable across structures; equal round-(i+1) histograms give equal round-i histograms, and after both colourings are stable equal histograms propagate to every later round, so the all-rounds form is the stable-colour comparison
--   - encoding: ≡_{k-proRCR} via the stable colouring χ_∞ and mult^A_k(c) = mult^B_k(c) for all stable colours c (Definition 1.7) → ProRCREquiv: for every round i and every canonical round-i colour c, the numbers of pro-tuples of A and of B with χ_i = c agree; reason: same all-rounds reading as for k-RCR (see the definition item)
--   - encoding: flat tuples and pro-tuples (α; t̄_1, …, t̄_m) with 1-based positions → flat tuples are List V; a pro-tuple is the pair (α, t̄_1 + ⋯ + t̄_m) as in §4; stp keeps the 1-based indices; reason: the arities in α recover the t̄_i, so the pair determines the pro-tuple
--   - reading: "let ≡_c denote a coarsest robust equivalence relation" (p. 35) → the conclusion asserts that one exists and that the four statements are equivalent for every one; reason: a coarsest relation is unique when it exists; asserting existence keeps the statement from being vacuous
-- source:
--   Aivasiliotis, Chen, Göbel, Lanzinger, Roth, Schneider, Homomorphism Indistinguishability Beyond Graphs, consolidated manuscript (catalogued as arXiv:2607.07934; sha256 671ba611…), p. 35, Theorem 4.14

import Mathlib
import Definitions.Def_HomIndGHW_RCR_Structures
import Definitions.Def_HomIndGHW_RCR_Refinement
import Definitions.Def_HomIndGHW_RCR_Robust

open Classical HomIndGHW.RCR.Structure

namespace HomIndGHW.RCR

/-- Theorem 4.14 = Theorem 1.8 (p. 35): a coarsest robust equivalence relation `≡_c` exists, and
for every such `≡_c` the following are equivalent: (1) k-RCR distinguishes `A`, `B`; (2) `≡_c`
distinguishes `A`, `B`; (3) `≡_c⁺ = 𝔈(≡_c)` distinguishes `A`, `B`; (4) k-proRCR distinguishes
`A`, `B`. -/
theorem theorem_4_14 {σ : Sig} [LinearOrder σ.Sym] (k : ℕ) (hk : 1 ≤ k) {V W : Type*}
    [Fintype V] [Fintype W] (A : Structure σ V) (B : Structure σ W) (hA : A.NoIsolated)
    (hB : B.NoIsolated) :
    (∃ Sc : Setoid (FT A B k), IsCoarsestRobust Sc) ∧
      ∀ Sc : Setoid (FT A B k), IsCoarsestRobust Sc →
        [RCRDistinguishes k A B, RelDistinguishes Sc, ProRelDistinguishes (plus Sc),
          ProRCRDistinguishes k A B].TFAE := by sorry

end HomIndGHW.RCR
