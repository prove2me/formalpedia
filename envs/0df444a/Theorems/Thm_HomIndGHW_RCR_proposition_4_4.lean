-- Prove2me | Theorems.Thm_HomIndGHW_RCR_proposition_4_4
-- name    : HomIndGHW.RCR.proposition_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:03:07.345684+00:00
-- url     : https://prove2.me/theorems/6d545733-b24a-44d2-ad15-289bb7cedd93
-- title:
--   Proposition 4.4 — the stable k-proRCR colouring of MCT_k(A) ∪ MCT_k(B) is the coarsest pro-robust equivalence relation
-- statement:
--   Let $k\ge1$, fix $\preceq_\sigma$, and let $\mathcal A,\mathcal B$ be finite $\sigma$-structures with disjoint domains (without isolated elements). Let $\approx_\infty$ be the equivalence relation induced by the stable $k$-proRCR colouring of $\mathrm{MCT}_k(\mathcal A)\cup\mathrm{MCT}_k(\mathcal B)$. Then
--
--   1. $\approx_\infty$ is pro-robust;
--   2. every pro-robust equivalence relation $\approx$ satisfies $\approx\ \subseteq\ \approx_\infty$.
--
--   Differences from the source:
--
--   - encoding: σ-structures, implicitly finite (#Hom is "the cardinality of a finite set", p. 14) → domains are types with [Fintype _]; relations are sets of tuples Fin (ar R) → V, hence finite; reason: finite domains are the paper's setting; a tuple of length ar(R) is a function on Fin (ar R)
--   - reading: σ-structures, which by Remark 2.1 (p. 14) and Remark 3.1 (p. 18) never have isolated elements → hypotheses A.NoIsolated, B.NoIsolated on every σ-structure of the statement; reason: the paper's standing assumption, stated once for the whole paper; the theorem's sentence relies on it
--   - encoding: a finite relational signature σ with positive arities and a fixed total order ⪯σ on its symbols → Sig (a finite type of symbols with ar_pos) and a [LinearOrder σ.Sym] binder; reason: the paper fixes an arbitrary total order (p. 6, p. 18); quantifying over every order covers each choice
--   - encoding: A, B "with disjoint domains", relations on T_k(A) ∪ T_k(B) (resp. MCT_k(A) ∪ MCT_k(B)) → domains V, W and the sum types FT A B k = T_k(A) ⊕ T_k(B), FP A B k = MCT_k(A) ⊕ MCT_k(B); equivalence relations are Setoids, ⊆ is ≤; reason: a disjoint union is a sum type; disjointness is automatic
--   - encoding: the equivalence relation induced by the stable colouring of the union → "same colour at every round" (rcrStable / proStable); reason: the round partitions refine each other and, once two consecutive ones coincide, all later ones do; their intersection is the stable partition
--   - encoding: flat tuples and pro-tuples (α; t̄_1, …, t̄_m) with 1-based positions → flat tuples are List V; a pro-tuple is the pair (α, t̄_1 + ⋯ + t̄_m) as in §4; stp keeps the 1-based indices; reason: the arities in α recover the t̄_i, so the pair determines the pro-tuple
-- source:
--   Aivasiliotis, Chen, Göbel, Lanzinger, Roth, Schneider, Homomorphism Indistinguishability Beyond Graphs, consolidated manuscript (catalogued as arXiv:2607.07934; sha256 671ba611…), p. 30, Proposition 4.4

import Mathlib
import Definitions.Def_HomIndGHW_RCR_Structures
import Definitions.Def_HomIndGHW_RCR_Refinement
import Definitions.Def_HomIndGHW_RCR_Robust

open Classical HomIndGHW.RCR.Structure

namespace HomIndGHW.RCR

/-- Proposition 4.4 (p. 30): for `A`, `B` with disjoint domains, the equivalence relation `≈_∞`
induced by the stable k-proRCR colouring of `MCT_k(A) ∪ MCT_k(B)` is pro-robust, and every
pro-robust equivalence relation is contained in it. -/
theorem proposition_4_4 {σ : Sig} [LinearOrder σ.Sym] (k : ℕ) (hk : 1 ≤ k) {V W : Type*}
    [Fintype V] [Fintype W] (A : Structure σ V) (B : Structure σ W) (hA : A.NoIsolated)
    (hB : B.NoIsolated) :
    ProRobust (proStable A B k) ∧
      ∀ S : Setoid (FP A B k), ProRobust S → S ≤ proStable A B k := by sorry

end HomIndGHW.RCR
