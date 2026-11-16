-- Prove2me | Theorems.Thm_LeeCutCertificates_Certificate_Supplement_tree_sparsifier_to_skeleton
-- name    : LeeCutCertificates.Certificate.Supplement.tree_sparsifier_to_skeleton
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:06:56.832245+00:00
-- url     : https://prove2.me/theorems/04a0d5ce-caf2-44c5-a642-9c1b56acec80
-- title:
--   Theorem 6 — From a tree cut sparsifier to a weak skeleton
-- statement:
--   Let $n\ge2$ and $B\ge1$. Given any explicit nonnegative capacitated tree $T$ with the $n$ vertices as distinct terminals, a deterministic program works for every hidden nonnegative graph $G$ with $\lambda(G)>0$ for which $T$ is a $B$-tree cut sparsifier. It returns an explicit graph $H$ satisfying
--
--   $$\lambda(H)\ge\lambda(G),\qquad c_H(S^*)\le\tfrac54\lambda(G)\quad\text{for every minimum-cut shore }S^*.$$
--
--   Its cap is `conversionCap(n,B)`, of order $nB L(n)^3K(n)^2$. Arbitrary Steiner vertices, internal terminals and zero capacities are allowed before offline normalization. This companion theorem is separate from the certificate goal.
--
--   **Formalization Note** The explicit budget is $2n+Q_{\rm ref}(n,2n,B)$, with $Q_{\rm ref}=400000\cdot268^2\cdot42^4(M+2n)B L^3K^2$. Its derivation from §4's normal form, §10.3's geometric sum and Appendix A's checkpoint bounds is recorded in MODERATION_NOTES.md. No minimum cut or its value is public input.
--
--   Differences from the source:
--   - encoding: finite graph vertices and exact deterministic query access → Fin n, the immutable real-capacity graph interface, and a well-founded OracleProgram selected before every hidden graph; reason: finite relabeling and explicit query traces preserve all instances; caps apply to every answer function
--   - generalization: an explicit B-tree cut sparsifier with O(n) vertices → any finite explicit B-tree cut sparsifier, with a cap independent of its original size; reason: §4 offline normalization bounds the retained topology; Appendix A explicitly removes the size restriction
--   - encoding: O(nB log^3(2n)(log log(2n))^2) queries → the public numeric conversionCap; reason: the primitive source budgets and geometric sum give this uniform envelope without changing linear dependence on B
-- source:
--   Troy Lee, Finding and Certifying Weighted Minimum Cuts with Cut Queries, STOC 2027 submission #474 (October 2026), Theorem 6, printed p.8 (PDF p.9); Appendix A, printed pp.53–56 (PDF pp.54–57)

import Definitions.Def_LeeCutCertificates_Certificate_Supplement_GraphAlgorithms
import Definitions.Def_LeeCutCertificates_Certificate_Supplement_TerminalTrees
import Definitions.Def_LeeCutCertificates_Certificate_Supplement_Budgets

set_option autoImplicit false
open SunMinCut.Cactus

namespace LeeCutCertificates.Certificate.Supplement

theorem tree_sparsifier_to_skeleton (n : ℕ) (hn : 2 ≤ n)
    (B : ℝ) (hB : 1 ≤ B) (T : CapacitatedTree n) :
    ∃ p : OracleProgram (Finset (Fin n)) (ExplicitGraph n),
      p.Capped (conversionCap n B) ∧
      ∀ (m : ℕ) (G : Graph n m), Nonnegative G → 0 < lam G →
        Approximates G T B → AllMinCutSkeleton G (p.run (cutw G)).1 := by sorry

end LeeCutCertificates.Certificate.Supplement
