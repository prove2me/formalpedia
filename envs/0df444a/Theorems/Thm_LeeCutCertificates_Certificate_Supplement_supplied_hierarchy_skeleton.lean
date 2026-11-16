-- Prove2me | Theorems.Thm_LeeCutCertificates_Certificate_Supplement_supplied_hierarchy_skeleton
-- name    : LeeCutCertificates.Certificate.Supplement.supplied_hierarchy_skeleton
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:09:53.241087+00:00
-- url     : https://prove2.me/theorems/454a3e32-1bed-4ee0-a000-95c1dc0b8ac9
-- title:
--   Theorem 21 — Supplied-hierarchy bound
-- statement:
--   Let $n\ge2$, $B\ge1$ and let $T$ be a supplied hierarchy with $M$ nonroot nodes. For every hidden nonnegative graph $G$ with $\lambda(G)>0$ satisfying $R_{T,G}(S^*)\le B\lambda(G)$ for every minimum cut, one deterministic program returns a weak skeleton $H$ preserving all of those cuts at factor $5/4$. Its cap is
--
--   $$M\bigl(1+4(q-1)(\lfloor\log_2n\rfloor+3)\bigr),\qquad q=\lceil200\cdot42^2B^2\rceil.$$
--
--   It does not receive $\lambda(G)$ or any optimum shore. For public $M=O(n)$ this is the source's $O(nB^2\log n)$ bound, independent of hierarchy depth. It is a companion theorem rather than an ingredient of the certificate goal.
--
--   **Formalization Note** Canonical cluster capacities are computed from $G$ and learned by the program; the leading $M$ pays for them. Empty and repeated clusters, unary nodes and free leaves remain allowed. Appendix A, printed p.55 (PDF p.56), supplies this exact cap.
--
--   Differences from the source:
--   - encoding: finite graph vertices and exact deterministic query access → Fin n, the immutable real-capacity graph interface, and a well-founded OracleProgram selected before every hidden graph; reason: finite relabeling and explicit query traces preserve all instances; caps apply to every answer function
--   - generalization: a supplied O(n)-node hierarchy → any finite supplied hierarchy, with its actual nonroot-node count M in the budget; reason: specializing to M≤cn gives the complete stated rate for each public c; no initial topology is excluded
--   - encoding: O(nB² log n) queries → the exact source checkpoint cap with q=ceil(200·42²B²); reason: Appendix A specifies the cap, and Remark 32 establishes the every-minimum-cut conclusion
-- source:
--   Troy Lee, Finding and Certifying Weighted Minimum Cuts with Cut Queries, STOC 2027 submission #474 (October 2026), Theorem 21, printed p.26 (PDF p.27); Appendix A, printed pp.53–56 (PDF pp.54–57)

import Definitions.Def_LeeCutCertificates_Certificate_Supplement_GraphAlgorithms
import Definitions.Def_LeeCutCertificates_Certificate_Supplement_Hierarchies
import Definitions.Def_LeeCutCertificates_Certificate_Supplement_Budgets

set_option autoImplicit false
open SunMinCut.Cactus

namespace LeeCutCertificates.Certificate.Supplement

theorem supplied_hierarchy_skeleton (n : ℕ) (hn : 2 ≤ n)
    (T : Hierarchy n) (B : ℝ) (hB : 1 ≤ B) :
    ∃ p : OracleProgram (Finset (Fin n)) (ExplicitGraph n),
      p.Capped (suppliedCap n (T.nodes - 1) B) ∧
      ∀ (m : ℕ) (G : Graph n m), Nonnegative G → 0 < lam G →
        T.Promise G B → AllMinCutSkeleton G (p.run (cutw G)).1 := by sorry

end LeeCutCertificates.Certificate.Supplement
