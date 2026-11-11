-- Prove2me | Theorems.Thm_HomIndGHW_RCR_theorem_4_13
-- name    : HomIndGHW.RCR.theorem_4_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:02:53.529428+00:00
-- url     : https://prove2.me/theorems/ef494c4a-ce9d-45ab-9bc6-533f7b958544
-- title:
--   Theorem 4.13 — 𝔈 : ≡ ↦ ≡⁺ is an isomorphism from robust to pro-robust equivalence relations
-- statement:
--   Let $k\ge1$, fix $\preceq_\sigma$, and let $\mathcal A,\mathcal B$ be finite $\sigma$-structures with disjoint domains (without isolated elements). The map $\mathfrak E:\equiv\mapsto\equiv^+$ is a well-defined map from robust to pro-robust equivalence relations, and it is an **isomorphism** in the sense of Definition 4.5: it is a bijection, and for all robust $\equiv,\equiv'$
--   $$\equiv\ \subseteq\ \equiv'\iff \equiv^+\ \subseteq\ \equiv'^+ .$$
--   It transports the coarsest robust relation to the coarsest pro-robust relation.
--
--   Differences from the source:
--
--   - encoding: σ-structures, implicitly finite (#Hom is "the cardinality of a finite set", p. 14) → domains are types with [Fintype _]; relations are sets of tuples Fin (ar R) → V, hence finite; reason: finite domains are the paper's setting; a tuple of length ar(R) is a function on Fin (ar R)
--   - reading: σ-structures, which by Remark 2.1 (p. 14) and Remark 3.1 (p. 18) never have isolated elements → hypotheses A.NoIsolated, B.NoIsolated on every σ-structure of the statement; reason: the paper's standing assumption, stated once for the whole paper; the theorem's sentence relies on it
--   - encoding: a finite relational signature σ with positive arities and a fixed total order ⪯σ on its symbols → Sig (a finite type of symbols with ar_pos) and a [LinearOrder σ.Sym] binder; reason: the paper fixes an arbitrary total order (p. 6, p. 18); quantifying over every order covers each choice
--   - encoding: A, B "with disjoint domains", relations on T_k(A) ∪ T_k(B) (resp. MCT_k(A) ∪ MCT_k(B)) → domains V, W and the sum types FT A B k = T_k(A) ⊕ T_k(B), FP A B k = MCT_k(A) ⊕ MCT_k(B); equivalence relations are Setoids, ⊆ is ≤; reason: a disjoint union is a sum type; disjointness is automatic
--   - encoding: flat tuples and pro-tuples (α; t̄_1, …, t̄_m) with 1-based positions → flat tuples are List V; a pro-tuple is the pair (α, t̄_1 + ⋯ + t̄_m) as in §4; stp keeps the 1-based indices; reason: the arities in α recover the t̄_i, so the pair determines the pro-tuple
--   - reading: "𝔈 is an isomorphism", 𝔈 being "a well-defined mapping from robust equivalence relations to pro-robust equivalence relations" (p. 32) → ∃ hE : (∀ robust ≡, ≡⁺ pro-robust), IsIsoRP (≡ ↦ ⟨≡⁺, hE ≡⟩); reason: the map exists by Proposition 4.6; the existential states that well-definedness together with the isomorphism property
-- source:
--   Aivasiliotis, Chen, Göbel, Lanzinger, Roth, Schneider, Homomorphism Indistinguishability Beyond Graphs, consolidated manuscript (catalogued as arXiv:2607.07934; sha256 671ba611…), p. 35, Theorem 4.13

import Mathlib
import Definitions.Def_HomIndGHW_RCR_Structures
import Definitions.Def_HomIndGHW_RCR_Refinement
import Definitions.Def_HomIndGHW_RCR_Robust

open Classical HomIndGHW.RCR.Structure

namespace HomIndGHW.RCR

/-- Theorem 4.13 (p. 35): `𝔈 : ≡ ↦ ≡⁺` is a well-defined map from robust to pro-robust
equivalence relations, and it is an isomorphism (Definition 4.5): a bijection with
`≡ ⊆ ≡′ ⇔ ≡⁺ ⊆ ≡′⁺`. -/
theorem theorem_4_13 {σ : Sig} [LinearOrder σ.Sym] (k : ℕ) (hk : 1 ≤ k) {V W : Type*}
    [Fintype V] [Fintype W] (A : Structure σ V) (B : Structure σ W) (hA : A.NoIsolated)
    (hB : B.NoIsolated) :
    ∃ hE : ∀ S : RobustRel A B k, ProRobust (plus S.1),
      IsIsoRP (fun S : RobustRel A B k => (⟨plus S.1, hE S⟩ : ProRobustRel A B k)) := by sorry

end HomIndGHW.RCR
