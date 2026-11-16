-- Prove2me | Theorems.Thm_LeeCutCertificates_Certificate_Supplement_deterministic_tree_cover
-- name    : LeeCutCertificates.Certificate.Supplement.deterministic_tree_cover
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:05:39.400655+00:00
-- url     : https://prove2.me/theorems/d7f43838-c2e5-4dce-87df-072205e4ec28
-- title:
--   Lemma 17 — A deterministic tree cover
-- statement:
--   For an explicit nonnegative weighted graph $H$ on $n\ge2$ vertices with $\lambda(H)>0$, there is a deterministic offline choice of a family $\mathcal T(H)$ of support spanning trees such that
--
--   $$|\mathcal T(H)|\le5(\lceil\log_2n\rceil+3),\qquad
--   c_H(S)\le\tfrac54\lambda(H)\ \Longrightarrow\ \exists T\in\mathcal T(H),\ |\partial_T(S)|\le2$$
--
--   for every nonempty proper shore $S$. The choice is a function of the explicit graph alone and makes no calls to any hidden graph $G$. It covers every near-minimum cut simultaneously and supports Theorem 4's complete reporting stage.
--
--   **Formalization Note** Appendix A, printed p.55 (PDF p.56), supplies the family-size constant. Trees may repeat; the size bound is unchanged.
--
--   Differences from the source:
--   - encoding: an arbitrary undirected supplied tree → a public root and parent map reaching that root; reason: every finite tree can be rooted offline; parent edges count each unordered edge once
--   - encoding: deterministically compute from explicit H with zero G queries → a single function H ↦ a finite list of trees; reason: the function receives only explicit H, with no hidden-graph or oracle argument; offline computation is free
--   - generalization: O(log n) spanning trees on V → spanning trees every edge of which has positive aggregate weight in H, at most 5(ceil(log₂ n)+3) of them; reason: the proof of Lemma 17 takes each tree inside a spanning set of positive-weight pairs of H (Lemma 16, printed pp.24–25, PDF pp.25–26), and Appendix A gives the count; dropping the positivity clause gives the source statement
-- source:
--   Troy Lee, Finding and Certifying Weighted Minimum Cuts with Cut Queries, STOC 2027 submission #474 (October 2026), Lemma 17, printed p.25 (PDF p.26); Appendix A, printed pp.53–56 (PDF pp.54–57)

import Definitions.Def_LeeCutCertificates_Certificate_Supplement_GraphAlgorithms
import Definitions.Def_LeeCutCertificates_Certificate_Supplement_Budgets

set_option autoImplicit false
open SunMinCut.Cactus

namespace LeeCutCertificates.Certificate.Supplement

theorem deterministic_tree_cover (n m : ℕ) (hn : 2 ≤ n) :
    ∃ cover : Graph n m → List (RootedTree n),
      ∀ H, Nonnegative H → 0 < lam H →
        (cover H).length ≤ 5 * (ceilLog2 n + 3) ∧
        (∀ T ∈ cover H, ∀ v, v ≠ T.root → 0 < pairWeight H v (T.parent v)) ∧
        ∀ S, Nontriv S → cutw H S ≤ (5 / 4 : ℝ) * lam H →
          ∃ T ∈ cover H, T.TwoRespects S := by sorry

end LeeCutCertificates.Certificate.Supplement
