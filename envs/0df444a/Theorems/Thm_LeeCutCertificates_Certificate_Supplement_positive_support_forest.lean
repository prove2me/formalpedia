-- Prove2me | Theorems.Thm_LeeCutCertificates_Certificate_Supplement_positive_support_forest
-- name    : LeeCutCertificates.Certificate.Supplement.positive_support_forest
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:04:54.942725+00:00
-- url     : https://prove2.me/theorems/635ef16b-098f-4f41-a52d-74eda37df83e
-- title:
--   Lemma 9 — Positive-support forest
-- statement:
--   Let $n\ge2$. One deterministic cut-oracle program works for every graph $G$ on $n$ vertices with arbitrary nonnegative real edge weights and returns a maximal spanning forest of its positive support, with the exact weights of the forest edges. Its number of queries is at most
--
--   $$3n+4n\lceil\log_2n\rceil\le7nL(n).$$
--
--   The forest has exactly the support's components, including isolated vertices; disconnected and all-zero graphs are included. This is the support information needed for the complete zero-value branch of Theorem 4.
--
--   **Formalization Note** A forest is acyclic, uses only positive aggregate-capacity edges and has the same reachability relation as the positive support. Appendix A, printed p.54 (PDF p.55), supplies the exact cap.
--
--   Differences from the source:
--   - encoding: finite graph vertices and exact deterministic query access → Fin n, the immutable real-capacity graph interface, and a well-founded OracleProgram selected before every hidden graph; reason: finite relabeling and explicit query traces preserve all instances; caps apply to every answer function
--   - generalization: a maximal spanning forest of the positive support is learned → the output also records, for every forest edge uv, its exact aggregate weight pairWeight G u v; reason: the proof of Lemma 9 learns the weight of each found edge (printed p.18, PDF p.19), and dropping this clause gives the source statement
-- source:
--   Troy Lee, Finding and Certifying Weighted Minimum Cuts with Cut Queries, STOC 2027 submission #474 (October 2026), Lemma 9, printed p.17 (PDF p.18); Appendix A, printed pp.53–56 (PDF pp.54–57)

import Definitions.Def_LeeCutCertificates_Certificate_Supplement_GraphAlgorithms
import Definitions.Def_LeeCutCertificates_Certificate_Supplement_Budgets

set_option autoImplicit false
open SunMinCut.Cactus

namespace LeeCutCertificates.Certificate.Supplement

theorem positive_support_forest (n : ℕ) (hn : 2 ≤ n) :
    ∃ p : OracleProgram (Finset (Fin n)) (ForestOutput n),
      p.Capped (3 * n + 4 * n * ceilLog2 n) ∧
      ∀ (m : ℕ) (G : Graph n m), Nonnegative G →
        CorrectForest G (p.run (cutw G)).1 := by sorry

end LeeCutCertificates.Certificate.Supplement
