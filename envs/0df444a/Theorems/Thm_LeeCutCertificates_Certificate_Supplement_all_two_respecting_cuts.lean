-- Prove2me | Theorems.Thm_LeeCutCertificates_Certificate_Supplement_all_two_respecting_cuts
-- name    : LeeCutCertificates.Certificate.Supplement.all_two_respecting_cuts
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:13:08.326784+00:00
-- url     : https://prove2.me/theorems/456797e0-d125-4bda-8bee-a199d97f11a4
-- title:
--   Theorem 52 — All two-respecting cuts at a lower level
-- statement:
--   Given $n\ge2$, any supplied tree $T$ on the vertices and a known real level $\ell>0$, one deterministic program works for every nonnegative graph $G$ for which every nontrivial cut crossing at most two tree edges has weight at least $\ell$. It returns exactly
--
--   $$\{S:\varnothing\ne S\ne V,\ |\partial_T(S)|\le2,\ c_G(S)=\ell\}$$
--
--   using at most $250n(\lceil\log_2n\rceil+1)$ cut queries on every answer path, independently of the number of shores reported. Both orientations, one-edge cuts and all ties are included. The output may be empty, $\ell$ need not equal $\lambda(G)$, and no positivity of $\lambda(G)$ is assumed. This is the companion reporting theorem.
--
--   **Formalization Note** Appendix A, printed p.56 (PDF p.57), supplies the exact coefficient 250. Output enumeration and deduplication cost no oracle calls. Supplied tree edges may be absent from the graph.
--
--   Differences from the source:
--   - encoding: finite graph vertices and exact deterministic query access → Fin n, the immutable real-capacity graph interface, and a well-founded OracleProgram selected before every hidden graph; reason: finite relabeling and explicit query traces preserve all instances; caps apply to every answer function
--   - encoding: an arbitrary undirected supplied tree → a public root and parent map reaching that root; reason: every finite tree can be rooted offline; parent edges count each unordered edge once
--   - encoding: O(n log n) cut queries, independent of the number reported → at most 250n(ceil(log₂ n)+1) actual queries and exact Finset membership; reason: Appendix A supplies the cap, while complements decode every oriented shore for free
-- source:
--   Troy Lee, Finding and Certifying Weighted Minimum Cuts with Cut Queries, STOC 2027 submission #474 (October 2026), Theorem 52, printed p.49 (PDF p.50); Appendix A, printed pp.53–56 (PDF pp.54–57)

import Definitions.Def_LeeCutCertificates_Certificate_Supplement_GraphAlgorithms
import Definitions.Def_LeeCutCertificates_Certificate_Supplement_Budgets

set_option autoImplicit false
open SunMinCut.Cactus

namespace LeeCutCertificates.Certificate.Supplement

theorem all_two_respecting_cuts (n : ℕ) (hn : 2 ≤ n)
    (T : RootedTree n) (ℓ : ℝ) (hℓ : 0 < ℓ) :
    ∃ p : OracleProgram (Finset (Fin n)) (Finset (Finset (Fin n))),
      p.Capped (250 * n * (ceilLog2 n + 1)) ∧
      ∀ (m : ℕ) (G : Graph n m), Nonnegative G →
        (∀ S, T.TwoRespects S → ℓ ≤ cutw G S) →
        ∀ S, S ∈ (p.run (cutw G)).1 ↔ T.TwoRespects S ∧ cutw G S = ℓ := by sorry

end LeeCutCertificates.Certificate.Supplement
