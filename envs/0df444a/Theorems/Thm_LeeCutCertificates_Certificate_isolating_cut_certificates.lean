-- Prove2me | Theorems.Thm_LeeCutCertificates_Certificate_isolating_cut_certificates
-- name    : LeeCutCertificates.Certificate.isolating_cut_certificates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:47:12.022392+00:00
-- url     : https://prove2.me/theorems/509f9b03-ac29-4620-ae2a-80c4e421d1f5
-- title:
--   Lemma 11 — Isolating-cut certificates
-- statement:
--   Let $G$ be a nonnegatively weighted undirected graph on $n\ge2$ vertices, and let $R\subseteq V$ have at least two terminals. For $v\in R$, write $\operatorname{iso}_G(v;R)$ for the minimum capacity of a shore containing $v$ and no other terminal of $R$. There is one finite query family $Q$ such that
--
--   $$|Q|\le9n\bigl(\lceil\log_2|R|\rceil+1\bigr),$$
--
--   and, simultaneously for every nonnegative competitor $G'$ consistent with its answers,
--
--   $$\operatorname{iso}_{G'}(v;R)=\operatorname{iso}_G(v;R)\qquad(v\in R).$$
--
--   This is a simultaneous certificate for all terminal isolating values, including zero values; terminals need not be independent and the graph need not be connected.
--
--   **Formalization Note** The integer logarithm is `Nat.clog 2 R.card`. The explicit uniform budget is Appendix A's $9n(\lceil\log_2|R|\rceil+1)$, printed p.54 (PDF p.55). Each isolating minimum ranges over a nonempty finite family of shores, because $v\in R$ and $|R|\ge2$. The same fixed family $Q$ serves every terminal and every consistent graph.
--
--   Differences from the source:
--   - encoding: finite labelled vertices with symmetric nonnegative real pair weights → Fin n with n≥2 and arbitrary nonnegative real edge records, aggregating parallel records and ignoring loops; all competitors have arbitrary independent record counts and endpoints; reason: every source weighting has an edge-record representation and all cuts and flows use its aggregate pair capacities; no support or connectivity restriction is added
--   - encoding: O(n log |R|) cut queries → 9n(ceilLog2 |R|+1) cut queries with ceilLog2 a=Nat.clog 2 a; reason: Appendix A, printed p.54 (PDF p.55), supplies the uniform integer-log budget
--   - encoding: the isolating minimum over S∩R={v} → terminalValue G {v} (R minus {v}), expressed as a real infimum; reason: the eligible shore families are equal, finite and nonempty on every theorem instance, so the infimum is the attained source minimum
-- source:
--   Troy Lee, Finding and Certifying Weighted Minimum Cuts with Cut Queries, STOC 2027 submission #474 (October 2026), Lemma 11, printed p.20 (PDF p.21), proof continuing on printed p.21 (PDF p.22); explicit budget, Appendix A, printed p.54 (PDF p.55); pinned PDF sha256 853e2745e72c36e8e0567917faa6eedd8dfe99b4078a34a70d8d4b81516c372d (citation_basis: published, submission artifact, not an acceptance claim).

import Mathlib
import Definitions.Def_LeeCutCertificates_Certificate_TreePatterns
import Definitions.Def_LeeCutCertificates_Certificate_Terminals

set_option autoImplicit false
open SunMinCut.Cactus

namespace LeeCutCertificates.Certificate

theorem isolating_cut_certificates {n m : ℕ} (hn : 2 ≤ n) (G : Graph n m)
    (hG : Nonnegative G) (R : Finset (Fin n)) (hR : 2 ≤ R.card) :
    ∃ Q : Finset (Finset (Fin n)),
      Q.card ≤ 9 * n * (ceilLog2 R.card + 1) ∧ IsolatingCertificate G R Q := by sorry

end LeeCutCertificates.Certificate
