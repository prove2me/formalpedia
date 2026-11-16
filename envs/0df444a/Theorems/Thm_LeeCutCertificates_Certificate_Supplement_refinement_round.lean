-- Prove2me | Theorems.Thm_LeeCutCertificates_Certificate_Supplement_refinement_round
-- name    : LeeCutCertificates.Certificate.Supplement.refinement_round
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:10:52.422999+00:00
-- url     : https://prove2.me/theorems/6cf661be-6580-40c9-95b9-83378b4a926b
-- title:
--   Lemma 30 — One refinement round
-- statement:
--   Fix $n\ge2$, $a=268L(n)K(n)$, $\rho_0=42$ and $\gamma=(100a^2\rho_0^2)^{-1}$. Given a hierarchy $T$ with $M$ nonroot nodes and a public $B\ge1/\gamma$, one deterministic program works for every nonnegative graph $G$ with positive minimum cut and the universal promise $R_{T,G}(S^*)\le B\lambda(G)$. It returns a new canonical hierarchy with at most $2n+1$ nodes and explicitly learned capacities satisfying
--
--   $$R_{\rm new}(S^*)\le(B/2)\lambda(G)\quad\text{for every original minimum cut }S^*.$$
--
--   With $q=\lceil2B/\gamma\rceil$, its cap is $M(1+4(q-1)(\lfloor\log_2n\rfloor+3))+2n$. For $M=O(n)$ this is $O(na^2B\log(2n))$. This is the refinement support for Theorem 31.
--
--   **Formalization Note** The initial hierarchy's canonical capacities are computed from $G$, rather than chosen independently. The cap includes their queries. The fixed parameters never depend on $\lambda$, a shore, the hierarchy depth or weight spread.
--
--   Differences from the source:
--   - encoding: finite graph vertices and exact deterministic query access → Fin n, the immutable real-capacity graph interface, and a well-founded OracleProgram selected before every hidden graph; reason: finite relabeling and explicit query traces preserve all instances; caps apply to every answer function
--   - generalization: an O(n)-cluster canonical hierarchy → any finite input hierarchy, retaining M explicitly in the cap; reason: the source completion and transfer bounds are linear in the actual cluster count
--   - encoding: an unspecified absolute offline a₀ and O(na²B log(2n)) queries → a₀=268, ρ₀=42, γ fixed from n, and the exact q-based round cap; reason: §10.3–10.4 and Appendix A give these constants, and Lemma 29 gives at most 2n new-capacity queries
--   - generalization: the hierarchy is replaced by one with promise (B/2)λ → the output is a hierarchy with childless terminals and at most 2n+1 nodes, returned together with its canonical capacities, which equal c_G of its clusters; reason: §9 (printed p.26, PDF p.27) states that every constructed hierarchy has at most 2n+1 nodes and Lemma 28 supplies that bound, while §10.2 queries the new capacities; dropping these clauses gives the source statement
-- source:
--   Troy Lee, Finding and Certifying Weighted Minimum Cuts with Cut Queries, STOC 2027 submission #474 (October 2026), Lemma 30, printed p.32 (PDF p.33); Appendix A, printed pp.53–56 (PDF pp.54–57)

import Definitions.Def_LeeCutCertificates_Certificate_Supplement_GraphAlgorithms
import Definitions.Def_LeeCutCertificates_Certificate_Supplement_Hierarchies
import Definitions.Def_LeeCutCertificates_Certificate_Supplement_Budgets

set_option autoImplicit false
open SunMinCut.Cactus

namespace LeeCutCertificates.Certificate.Supplement

theorem refinement_round (n : ℕ) (hn : 2 ≤ n)
    (T : Hierarchy n) (B : ℝ) (hB : 1 / gamma n ≤ B) :
    ∃ p : OracleProgram (Finset (Fin n)) (RefinedHierarchy n),
      p.Capped (roundCap n (T.nodes - 1) B) ∧
      ∀ (m : ℕ) (G : Graph n m), Nonnegative G → 0 < lam G → T.Promise G B →
        let o := (p.run (cutw G)).1
        o.topology.nodes ≤ 2 * n + 1 ∧
        o.capacity = o.topology.canonical G ∧ o.topology.Promise G (B / 2) := by sorry

end LeeCutCertificates.Certificate.Supplement
