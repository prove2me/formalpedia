-- Prove2me | Theorems.Thm_HomIndGHW_RCR_proposition_4_2
-- name    : HomIndGHW.RCR.proposition_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:02:41.466487+00:00
-- url     : https://prove2.me/theorems/f2a39c0b-60da-4a85-8029-eb90bb89f896
-- title:
--   Proposition 4.2 — the stable k-RCR colouring of T_k(A) ∪ T_k(B) is the coarsest robust equivalence relation
-- statement:
--   Let $k\ge1$ and $\mathcal A,\mathcal B$ finite $\sigma$-structures with disjoint domains (without isolated elements). Let $\equiv_\infty$ be the equivalence relation induced by the stable $k$-RCR colouring of $T_k(\mathcal A)\cup T_k(\mathcal B)$. Then
--
--   1. $\equiv_\infty$ is robust;
--   2. every robust equivalence relation $\equiv$ satisfies $\equiv\ \subseteq\ \equiv_\infty$.
--
--   So $\equiv_\infty$ is the coarsest robust equivalence relation.
--
--   Differences from the source:
--
--   - encoding: σ-structures, implicitly finite (#Hom is "the cardinality of a finite set", p. 14) → domains are types with [Fintype _]; relations are sets of tuples Fin (ar R) → V, hence finite; reason: finite domains are the paper's setting; a tuple of length ar(R) is a function on Fin (ar R)
--   - reading: σ-structures, which by Remark 2.1 (p. 14) and Remark 3.1 (p. 18) never have isolated elements → hypotheses A.NoIsolated, B.NoIsolated on every σ-structure of the statement; reason: the paper's standing assumption, stated once for the whole paper; the theorem's sentence relies on it
--   - encoding: a finite relational signature σ with positive arities → Sig (a finite type of symbols, arities with ar_pos); reason: same objects; the symbols are an arbitrary finite type
--   - encoding: A, B "with disjoint domains", relations on T_k(A) ∪ T_k(B) (resp. MCT_k(A) ∪ MCT_k(B)) → domains V, W and the sum types FT A B k = T_k(A) ⊕ T_k(B), FP A B k = MCT_k(A) ⊕ MCT_k(B); equivalence relations are Setoids, ⊆ is ≤; reason: a disjoint union is a sum type; disjointness is automatic
--   - encoding: the equivalence relation induced by the stable colouring of the union → "same colour at every round" (rcrStable / proStable); reason: the round partitions refine each other and, once two consecutive ones coincide, all later ones do; their intersection is the stable partition
--   - encoding: flat tuples and pro-tuples (α; t̄_1, …, t̄_m) with 1-based positions → flat tuples are List V; a pro-tuple is the pair (α, t̄_1 + ⋯ + t̄_m) as in §4; stp keeps the 1-based indices; reason: the arities in α recover the t̄_i, so the pair determines the pro-tuple
-- source:
--   Aivasiliotis, Chen, Göbel, Lanzinger, Roth, Schneider, Homomorphism Indistinguishability Beyond Graphs, consolidated manuscript (catalogued as arXiv:2607.07934; sha256 671ba611…), p. 30, Proposition 4.2

import Mathlib
import Definitions.Def_HomIndGHW_RCR_Structures
import Definitions.Def_HomIndGHW_RCR_Refinement
import Definitions.Def_HomIndGHW_RCR_Robust

open Classical HomIndGHW.RCR.Structure

namespace HomIndGHW.RCR

/-- Proposition 4.2 (p. 30): for `A`, `B` with disjoint domains, the equivalence relation `≡_∞`
induced by the stable k-RCR colouring of `T_k(A) ∪ T_k(B)` is robust, and every robust equivalence
relation is contained in it. -/
theorem proposition_4_2 {σ : Sig} (k : ℕ) (hk : 1 ≤ k) {V W : Type*} [Fintype V] [Fintype W]
    (A : Structure σ V) (B : Structure σ W) (hA : A.NoIsolated) (hB : B.NoIsolated) :
    Robust (rcrStable A B k) ∧
      ∀ S : Setoid (FT A B k), Robust S → S ≤ rcrStable A B k := by sorry

end HomIndGHW.RCR
