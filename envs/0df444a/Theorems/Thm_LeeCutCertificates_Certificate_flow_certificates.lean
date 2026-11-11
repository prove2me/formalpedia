-- Prove2me | Theorems.Thm_LeeCutCertificates_Certificate_flow_certificates
-- name    : LeeCutCertificates.Certificate.flow_certificates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:47:02.497673+00:00
-- url     : https://prove2.me/theorems/51dee27c-6c4c-4d36-928c-293c97c53224
-- title:
--   Lemma 2 — Flow certificates
-- statement:
--   Let $G$ be a nonnegatively weighted undirected graph on $n\ge2$ labelled vertices, allowing zero weights and disconnected support. A signed flow $f$ has $|f(u,v)|\le w_G(u,v)$ and net outflow $b(v)=\sum_u f(v,u)$.
--
--   1. For every feasible divergence vector $b$, there is a spanning tree $T$ of the complete labelled graph whose prescribed query family $Q(T)$ satisfies
--
--   $$|Q(T)|\le4n-1,\qquad \forall G'\ge0,\quad G'\text{ agrees on }Q(T)\Longrightarrow b\text{ is feasible in }G'.$$
--
--   The shores of $Q(T)$ depend only on $T$ and the labels, independently of $G$ and $b$ once $T$ is fixed. The realizing flow may differ between competitors.
--
--   2. For every distinct $s,t$, there are at most $4n$ query shores, including an optimum $s$–$t$ shore $S^*$, that preserve both the minimum separating-cut value and optimality of $S^*$ in every consistent nonnegative graph.
--
--   3. For every disjoint nonempty pair $A,B\subseteq V$, the minimum $A$–$B$ separating-cut value has a certificate with at most $8n+1$ queries.
--
--   This result provides certificate interfaces for arbitrary feasible divergences, individual terminal pairs, and terminal sets.
--
--   **Formalization Note** The exact $4n-1$ and $4n$ constants are the printed lemma's constants. The terminal-set budget $8n+1$ is the explicit form in Appendix A, printed p.53 (PDF p.54), rather than an instance-dependent interpretation of $O(n)$. Competitors may have arbitrary edge counts and endpoints. The complete-graph tree is not restricted to positive-capacity pairs.
--
--   Differences from the source:
--   - encoding: finite labelled vertices with symmetric nonnegative real pair weights → Fin n with n≥2 and arbitrary nonnegative real edge records, aggregating parallel records and ignoring loops; all competitors have arbitrary independent record counts and endpoints; reason: every source weighting has an edge-record representation and all cuts and flows use its aggregate pair capacities; no support or connectivity restriction is added
--   - encoding: a labelled spanning tree determines queried shores → the explicitly defined family treeQueries T with fixed costs, normalized potentials and outgoing sets of §7.1; reason: the family is constructed from T alone, retaining the full source clause
--   - encoding: an O(n) terminal-set certificate → a certificate of at most 8n+1 shores; reason: Appendix A, printed p.53 (PDF p.54), supplies this uniform explicit budget; the separate exact 4n−1 and 4n clauses are unchanged
-- source:
--   Troy Lee, Finding and Certifying Weighted Minimum Cuts with Cut Queries, STOC 2027 submission #474 (October 2026), Lemma 2, printed pp.3–4 (PDF pp.4–5); complete proof §7.1, printed pp.18–20 (PDF pp.19–21); explicit terminal-set budget, Appendix A, printed p.53 (PDF p.54); pinned PDF sha256 853e2745e72c36e8e0567917faa6eedd8dfe99b4078a34a70d8d4b81516c372d (citation_basis: published, submission artifact, not an acceptance claim).

import Mathlib
import Definitions.Def_LeeCutCertificates_Certificate_TreePatterns
import Definitions.Def_LeeCutCertificates_Certificate_Terminals

set_option autoImplicit false
open SunMinCut.Cactus

namespace LeeCutCertificates.Certificate

theorem flow_certificates {n m : ℕ} (hn : 2 ≤ n) (G : Graph n m)
    (hG : Nonnegative G) :
    (∀ b : Fin n → ℝ, FeasibleDivergence G b →
      ∃ T : SimpleGraph (Fin n), T.IsTree ∧
        (treeQueries T).card ≤ 4 * n - 1 ∧ FlowCertificate G b (treeQueries T)) ∧
    (∀ s t : Fin n, s ≠ t →
      ∃ (Q : Finset (Finset (Fin n))) (S : Finset (Fin n)),
        Q.card ≤ 4 * n ∧ TerminalWitnessCertificate G {s} {t} Q S) ∧
    (∀ A B : Finset (Fin n), A.Nonempty → B.Nonempty → Disjoint A B →
      ∃ Q : Finset (Finset (Fin n)),
        Q.card ≤ 8 * n + 1 ∧ TerminalValueCertificate G A B Q) := by sorry

end LeeCutCertificates.Certificate
