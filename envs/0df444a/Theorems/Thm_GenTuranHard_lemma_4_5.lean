-- Prove2me | Theorems.Thm_GenTuranHard_lemma_4_5
-- name    : GenTuranHard.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:36:11.411741+00:00
-- url     : https://prove2.me/theorems/b36ff421-b601-4e38-af98-be4238e0b75f
-- title:
--   Lemma 4.5 — the lexicographically largest edge-bearing sequence ends in $K_2 \cup qK_1$
-- statement:
--   Let $T$ be a bipartite graph with $e(T) > 0$ and $s = v(T) - 2$. Among all sequences $(I_1, \dots, I_s)$ satisfying (4.1) for which $e(T_s) > 0$, choose one with the lexicographically largest exponent vector $(|I_1|, \dots, |I_s|)$ (first coordinate most significant). Then $p(T_s) = 2$, and consequently
--
--   $$
--   T_s \cong K_2 \cup qK_1 \quad \text{for some integer } q \ge 0.
--   $$
--
--   This identifies the leading monomial of the expansion carrying an edge, which makes $e(G)$ the dominant term of $\hom(T, L_{\mathbf x}(G))$ (Lemma 4.6).
--
--   **Formalization Note** "Choose one with the lexicographically largest exponent vector" is encoded as: the sequence has $e(T_s) > 0$, and no sequence with an edge-bearing terminal graph has a lexicographically larger exponent vector (all vectors have length $s$).
--
--   Differences from the source:
--   - encoding: the vertices of Q_I (classes of V(Q)∖I and new isolated vertices v′) → quotGraph Q I renumbered on Fin v(Q_I) by a fixed bijection; reason: homomorphism counts, vertex counts, p(·), edges and bipartiteness do not depend on the numbering
--   - encoding: a sequence chosen with the lexicographically largest exponent vector → any sequence Is with e(T_s) > 0 such that no such sequence has a lexicographically larger exponent vector (List.Lex (· < ·)); reason: lexicographic order on vectors of the same length is total, so these are exactly the maximal choices
--   - generalization: v(T) ≥ 3 (the standing assumption of §4, p.12) → every bipartite T with e(T) > 0 (v(T) ≥ 2, s = v(T) − 2 ≥ 0); reason: for v(T) = 2 the only sequence is the empty one and T_0 = T = K₂ has p = 2; the source's case v(T) ≥ 3 is included
-- source:
--   Chen, He, Li, Ma, Xie, NP-hardness of additive approximation for generalized Turán problems, arXiv:2610.16358 (sha256 dc85633a…), Lemma 4.5, p.15

import Mathlib
import Definitions.Def_GenTuranHard_validSeqs

set_option autoImplicit false

namespace GenTuranHard

/-- **Lemma 4.5** (Chen, He, Li, Ma, Xie, arXiv:2610.16358, sha256 dc85633a…, Lemma 4.5, p.15). Let `T`
be a bipartite graph with `e(T) > 0` and `s = v(T) − 2`. Among all sequences `(I₁, …, I_s)` of (4.1) with
`e(T_s) > 0`, choose one with the lexicographically largest exponent vector `(|I₁|, …, |I_s|)`. Then
`p(T_s) = 2`, and consequently `T_s ≅ K₂ ∪ qK₁` for some integer `q ≥ 0`.

**Formalization Note** The chosen sequence `Is` has `e(T_s) > 0` and no sequence `Js` with
`e(T_s(Js)) > 0` has a lexicographically larger exponent vector (`List.Lex (· < ·)`, first coordinate
most significant; all vectors have length `s`). `K₂ ∪ qK₁` is `edgePlusIsolated q`. -/
theorem lemma_4_5 {W : Type} [Fintype W] (T : SimpleGraph W) (hT : T.IsBipartite)
    (hTe : T.edgeSet.Nonempty) (Is : List (Finset ℕ))
    (hIs : Is ∈ validSeqs (Fintype.card W - 2) (toFin T))
    (hIe : (termGraph (toFin T) Is).2.edgeSet.Nonempty)
    (hmax : ∀ Js ∈ validSeqs (Fintype.card W - 2) (toFin T),
      (termGraph (toFin T) Js).2.edgeSet.Nonempty → ¬ List.Lex (· < ·) (expVec Is) (expVec Js)) :
    pNon (termGraph (toFin T) Is) = 2 ∧
      ∃ q : ℕ, Nonempty ((termGraph (toFin T) Is).2 ≃g edgePlusIsolated q) := by sorry

end GenTuranHard
