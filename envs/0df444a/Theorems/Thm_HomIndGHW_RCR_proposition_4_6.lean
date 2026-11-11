-- Prove2me | Theorems.Thm_HomIndGHW_RCR_proposition_4_6
-- name    : HomIndGHW.RCR.proposition_4_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:02:32.729936+00:00
-- url     : https://prove2.me/theorems/b77ea2ff-196f-43b1-aed1-7dc30f6b96a8
-- title:
--   Proposition 4.6 — ≡⁺ is pro-robust for every robust ≡
-- statement:
--   Let $k\ge1$, fix $\preceq_\sigma$, and let $\mathcal A,\mathcal B$ be finite $\sigma$-structures with disjoint domains (without isolated elements). For every robust equivalence relation $\equiv$ on $T_k(\mathcal A)\cup T_k(\mathcal B)$, the relation $\equiv^+$ on $\mathrm{MCT}_k(\mathcal A)\cup\mathrm{MCT}_k(\mathcal B)$ given by
--   $$(\alpha,s)\equiv^+(\alpha',s')\iff\alpha=\alpha'\ \text{and}\ s\equiv s'$$
--   is pro-robust. Hence $\mathfrak E:\equiv\mapsto\equiv^+$ maps robust to pro-robust relations.
--
--   Differences from the source:
--
--   - encoding: σ-structures, implicitly finite (#Hom is "the cardinality of a finite set", p. 14) → domains are types with [Fintype _]; relations are sets of tuples Fin (ar R) → V, hence finite; reason: finite domains are the paper's setting; a tuple of length ar(R) is a function on Fin (ar R)
--   - reading: σ-structures, which by Remark 2.1 (p. 14) and Remark 3.1 (p. 18) never have isolated elements → hypotheses A.NoIsolated, B.NoIsolated on every σ-structure of the statement; reason: the paper's standing assumption, stated once for the whole paper; the theorem's sentence relies on it
--   - encoding: a finite relational signature σ with positive arities and a fixed total order ⪯σ on its symbols → Sig (a finite type of symbols with ar_pos) and a [LinearOrder σ.Sym] binder; reason: the paper fixes an arbitrary total order (p. 6, p. 18); quantifying over every order covers each choice
--   - encoding: A, B "with disjoint domains", relations on T_k(A) ∪ T_k(B) (resp. MCT_k(A) ∪ MCT_k(B)) → domains V, W and the sum types FT A B k = T_k(A) ⊕ T_k(B), FP A B k = MCT_k(A) ⊕ MCT_k(B); equivalence relations are Setoids, ⊆ is ≤; reason: a disjoint union is a sum type; disjointness is automatic
--   - encoding: flat tuples and pro-tuples (α; t̄_1, …, t̄_m) with 1-based positions → flat tuples are List V; a pro-tuple is the pair (α, t̄_1 + ⋯ + t̄_m) as in §4; stp keeps the 1-based indices; reason: the arities in α recover the t̄_i, so the pair determines the pro-tuple
-- source:
--   Aivasiliotis, Chen, Göbel, Lanzinger, Roth, Schneider, Homomorphism Indistinguishability Beyond Graphs, consolidated manuscript (catalogued as arXiv:2607.07934; sha256 671ba611…), p. 32, Proposition 4.6

import Mathlib
import Definitions.Def_HomIndGHW_RCR_Structures
import Definitions.Def_HomIndGHW_RCR_Refinement
import Definitions.Def_HomIndGHW_RCR_Robust

open Classical HomIndGHW.RCR.Structure

namespace HomIndGHW.RCR

/-- Proposition 4.6 (p. 32): for a robust equivalence relation `≡` on `T_k(A) ∪ T_k(B)`, the
relation `≡⁺` (`(α, s) ≡⁺ (α′, s′)` iff `α = α′` and `s ≡ s′`) is pro-robust. -/
theorem proposition_4_6 {σ : Sig} [LinearOrder σ.Sym] (k : ℕ) (hk : 1 ≤ k) {V W : Type*}
    [Fintype V] [Fintype W] (A : Structure σ V) (B : Structure σ W) (hA : A.NoIsolated)
    (hB : B.NoIsolated) (S : Setoid (FT A B k)) (hS : Robust S) :
    ProRobust (plus S) := by sorry

end HomIndGHW.RCR
