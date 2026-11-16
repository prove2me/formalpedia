-- Prove2me | Theorems.Thm_LeeCutCertificates_Certificate_Supplement_linear_hierarchy_skeleton
-- name    : LeeCutCertificates.Certificate.Supplement.linear_hierarchy_skeleton
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:11:28.963687+00:00
-- url     : https://prove2.me/theorems/fbc339d5-2d8a-4efc-b5a5-56314bfa19eb
-- title:
--   Theorem 31 — Linear dependence on the hierarchy bound
-- statement:
--   Let $n\ge2$, $B\ge1$ and let $T$ be a supplied canonical hierarchy with $M$ nonroot clusters. One deterministic program, chosen before the hidden graph, works for every nonnegative graph $G$ with $\lambda(G)>0$ and $R_{T,G}(S^*)\le B\lambda(G)$ for every minimum cut. It returns a weak skeleton for all original minimum cuts and uses at most
--
--   $$400000\cdot268^2\cdot42^4\,(M+2n)B L(n)^3K(n)^2$$
--
--   queries on every answer path. For $M=O(n)$ this is exactly the stated $O(nB\log^3(2n)(\log\log(2n))^2)$ rate, with no depth, weight-spread or $\log B$ multiplier. Offline computation is unrestricted. This is a companion theorem of the certificate goal.
--
--   **Formalization Note** Section 10.3's geometric sum and Appendix A's checkpoint caps supply the displayed envelope. The initial size coefficient is retained; all later hierarchies have at most $2n$ nonroot nodes. The algorithm learns the initial canonical capacities and does not receive an optimum or its value.
--
--   Differences from the source:
--   - encoding: finite graph vertices and exact deterministic query access → Fin n, the immutable real-capacity graph interface, and a well-founded OracleProgram selected before every hidden graph; reason: finite relabeling and explicit query traces preserve all instances; caps apply to every answer function
--   - generalization: a canonical O(n)-node supplied hierarchy → any finite supplied topology with canonical capacities computed from G and its size M retained; reason: M≤cn gives the stated rate for every public supplied-size coefficient
--   - encoding: O(nB log³(2n)(log log(2n))²) queries → the displayed explicit numeric refinement envelope; reason: the source geometric sum and q-based primitive caps give this uniform bound; derivation is in MODERATION_NOTES.md
-- source:
--   Troy Lee, Finding and Certifying Weighted Minimum Cuts with Cut Queries, STOC 2027 submission #474 (October 2026), Theorem 31, printed p.32 (PDF p.33); Appendix A, printed pp.53–56 (PDF pp.54–57)

import Definitions.Def_LeeCutCertificates_Certificate_Supplement_GraphAlgorithms
import Definitions.Def_LeeCutCertificates_Certificate_Supplement_Hierarchies
import Definitions.Def_LeeCutCertificates_Certificate_Supplement_Budgets

set_option autoImplicit false
open SunMinCut.Cactus

namespace LeeCutCertificates.Certificate.Supplement

theorem linear_hierarchy_skeleton (n : ℕ) (hn : 2 ≤ n)
    (T : Hierarchy n) (B : ℝ) (hB : 1 ≤ B) :
    ∃ p : OracleProgram (Finset (Fin n)) (ExplicitGraph n),
      p.Capped (refinementCap n (T.nodes - 1) B) ∧
      ∀ (m : ℕ) (G : Graph n m), Nonnegative G → 0 < lam G →
        T.Promise G B → AllMinCutSkeleton G (p.run (cutw G)).1 := by sorry

end LeeCutCertificates.Certificate.Supplement
