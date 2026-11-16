-- Prove2me | Theorems.Thm_LeeCutCertificates_Certificate_Supplement_two_respecting_cut
-- name    : LeeCutCertificates.Certificate.Supplement.two_respecting_cut
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:08:40.353189+00:00
-- url     : https://prove2.me/theorems/b26ba7d0-7581-43f0-bbe8-7c2a76515bbf
-- title:
--   Theorem 19 — Two-respecting cuts
-- statement:
--   Let $n\ge2$ and let $T$ be any supplied tree on the graph's vertices. A deterministic program, chosen from $n$ and $T$ alone, works for every nonnegative real weighted graph $G$ and returns a nonempty proper shore $S$ attaining
--
--   $$\min_{\varnothing\ne U\ne V,\ |\partial_T(U)|\le2}c_G(U)$$
--
--   using at most $72n(\lceil\log_2n\rceil+1)$ cut queries on every answer path. One-edge and zero-weight cuts are included. No tree edge is required to be present in $G$. This is the companion two-respecting search theorem.
--
--   **Formalization Note** Appendix A, printed p.55 (PDF p.56), supplies the exact coefficient 72; the output asserts minimization and eligibility, not just the numerical infimum.
--
--   Differences from the source:
--   - encoding: finite graph vertices and exact deterministic query access → Fin n, the immutable real-capacity graph interface, and a well-founded OracleProgram selected before every hidden graph; reason: finite relabeling and explicit query traces preserve all instances; caps apply to every answer function
--   - encoding: an arbitrary undirected supplied tree → a public root and parent map reaching that root; reason: every finite tree can be rooted offline; parent edges count each unordered edge once
--   - encoding: O(n log n) queries → at most 72 n (ceil(log₂ n)+1) actual queries; reason: the exact source cap is in Appendix A
-- source:
--   Troy Lee, Finding and Certifying Weighted Minimum Cuts with Cut Queries, STOC 2027 submission #474 (October 2026), Theorem 19, printed p.25 (PDF p.26); Appendix A, printed pp.53–56 (PDF pp.54–57)

import Definitions.Def_LeeCutCertificates_Certificate_Supplement_GraphAlgorithms
import Definitions.Def_LeeCutCertificates_Certificate_Supplement_Budgets

set_option autoImplicit false
open SunMinCut.Cactus

namespace LeeCutCertificates.Certificate.Supplement

theorem two_respecting_cut (n : ℕ) (hn : 2 ≤ n) (T : RootedTree n) :
    ∃ p : OracleProgram (Finset (Fin n)) (Finset (Fin n)),
      p.Capped (72 * n * (ceilLog2 n + 1)) ∧
      ∀ (m : ℕ) (G : Graph n m), Nonnegative G →
        CorrectTwoRespecting G T (p.run (cutw G)).1 := by sorry

end LeeCutCertificates.Certificate.Supplement
