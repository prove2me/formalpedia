-- Prove2me | Theorems.Thm_LeeCutCertificates_Certificate_near_linear_mincut_certificates
-- name    : LeeCutCertificates.Certificate.near_linear_mincut_certificates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:47:16.708282+00:00
-- url     : https://prove2.me/theorems/4da49b51-7249-4cb5-8721-4aa8246d600f
-- title:
--   Theorem 1 — Near-linear certificates for exact weighted minimum cut
-- statement:
--   Let $G$ be any undirected graph on $n\ge2$ vertices with arbitrary nonnegative real capacities. A value certificate is a finite family $Q$ of exact cut queries for which every consistent nonnegative graph $G'$ on the same vertices has $\lambda(G')=\lambda(G)$. The competitor may put positive capacity on any pair, including pairs absent from $G$. Let $\operatorname{cert}(G)$ be the minimum cardinality of such a family and put $L=\lceil\log_2(2n)\rceil$.
--
--   There are a query family $Q$ and a nonempty proper shore $S^*\in Q$ such that
--
--   $$|Q|\le18nL^2,\qquad \operatorname{cert}(G)\le18nL^2,$$
--
--   $S^*$ is a minimum cut of $G$, and every nonnegative graph $G'$ agreeing on $Q$ satisfies
--
--   $$\lambda(G')=\lambda(G),\qquad S^*\text{ is a minimum-cut shore of }G'.$$
--
--   The minimum defining $\operatorname{cert}(G)$ is attained by some value-certificate family $Q_{\min}$. If $\lambda(G)=0$, the chosen family itself is $Q=\{S^*\}$ and $\operatorname{cert}(G)=1$.
--
--   This recovers the full source theorem, including persistence of a queried optimal shore and the original zero case. It concerns certificates chosen with full knowledge of $G$, rather than an algorithm to discover their queries.
--
--   **Formalization Note** The integer logarithm is `Nat.clog 2 (2*n)`, and the uniform $18nL^2$ budget, attainment, and zero-value complexity are recorded in Appendix A, printed p.53 (PDF p.54). In the proof's budget accounting, at most $L-1$ rounds each cost at most $9nL+8n$, and one optimum-shore query gives $(L-1)(9nL+8n)+1\le18nL^2$ for $n\ge2$. Certificate predicates unfold to cut equalities and universal optimality assertions; they contain no assumed resource guarantee.
--
--   Differences from the source:
--   - encoding: finite labelled vertices with symmetric nonnegative real pair weights → Fin n with n≥2 and arbitrary nonnegative real edge records, aggregating parallel records and ignoring loops; all competitors have arbitrary independent record counts and endpoints; reason: every source weighting has an edge-record representation and all cuts and flows use its aggregate pair capacities; no support or connectivity restriction is added
--   - encoding: cert(G)=O(n log²(2n)), with a persistent queried optimum shore and the singleton zero case → the uniform 18n(ceilLog2(2n))² bound, with a witnessed certificate, attained minimum, and cert(G)=1 when λ(G)=0; reason: Appendix A, printed p.53 (PDF p.54), states the explicit budget, attainment and zero-value identity; ceilLog2 is the integer ceiling logarithm
-- source:
--   Troy Lee, Finding and Certifying Weighted Minimum Cuts with Cut Queries, STOC 2027 submission #474 (October 2026), Theorem 1, printed p.3 (PDF p.4); proof printed pp.22–23 (PDF pp.23–24); Eq. (1) printed p.2 (PDF p.3); explicit bound, attained certificate minimum and zero case, Appendix A, printed p.53 (PDF p.54); pinned PDF sha256 853e2745e72c36e8e0567917faa6eedd8dfe99b4078a34a70d8d4b81516c372d (citation_basis: published, submission artifact, not an acceptance claim).

import Mathlib
import Definitions.Def_LeeCutCertificates_Certificate_TreePatterns
import Definitions.Def_LeeCutCertificates_Certificate_Terminals

set_option autoImplicit false
open SunMinCut.Cactus

namespace LeeCutCertificates.Certificate

theorem near_linear_mincut_certificates {n m : ℕ} (hn : 2 ≤ n) (G : Graph n m)
    (hG : Nonnegative G) :
    ∃ (Q : Finset (Finset (Fin n))) (S : Finset (Fin n)),
      WitnessCertificate G Q S ∧ Q.card ≤ 18 * n * (ceilLog2 (2 * n)) ^ 2 ∧
      cert G ≤ 18 * n * (ceilLog2 (2 * n)) ^ 2 ∧
      (∃ Qmin : Finset (Finset (Fin n)), ValueCertificate G Qmin ∧ Qmin.card = cert G) ∧
      (lam G = 0 → Q = {S} ∧ cert G = 1) := by sorry

end LeeCutCertificates.Certificate
