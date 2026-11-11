-- Prove2me | Theorems.Thm_LeeCutCertificates_Certificate_flow_to_half_terminals
-- name    : LeeCutCertificates.Certificate.flow_to_half_terminals
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:47:31.601399+00:00
-- url     : https://prove2.me/theorems/c7d77bd8-df64-4458-8020-a741b7be2ab5
-- title:
--   Lemma 13 — A flow to half the terminals
-- statement:
--   Let $G$ be a nonnegatively weighted undirected graph on $n\ge2$ vertices with $\lambda=\lambda(G)>0$. Let $U\subseteq V$ have at least two terminals. There exist a nonempty proper subset $R\subsetneq U$, a feasible signed flow $f$ in the original graph, and a finite query family $Q$, such that
--
--   $$2|R|\le|U|,\qquad |Q|\le8n,$$
--
--   and its net-outflow divergence $b(v)=\sum_u f(v,u)$ satisfies
--
--   $$b(u)=\lambda/2\ (u\in U\setminus R),\qquad b(v)=0\ (v\notin U),\qquad b(v)\le0\ (v\in R).$$
--
--   Moreover, in every consistent nonnegative graph $G'$ and for every shore $S$ disjoint from $R$,
--
--   $$c_{G'}(S)\ge\frac{\lambda}{2}|S\cap U|.$$
--
--   The value $\lambda$ is held fixed from $G$ across all competitors. This is a retained-terminal flow statement together with its full certified family of cut inequalities.
--
--   **Formalization Note** All flows remain on the original vertex set. The cardinality condition uses doubled natural cardinalities to avoid rounded division. The explicit $8n$ certificate budget is recorded in Appendix A, printed p.54 (PDF p.55). No lower bound on the competitor's global minimum cut is assumed.
--
--   Differences from the source:
--   - encoding: finite labelled vertices with symmetric nonnegative real pair weights → Fin n with n≥2 and arbitrary nonnegative real edge records, aggregating parallel records and ignoring loops; all competitors have arbitrary independent record counts and endpoints; reason: every source weighting has an edge-record representation and all cuts and flows use its aggregate pair capacities; no support or connectivity restriction is added
--   - encoding: a retained set with |R|≤|U|/2 → 2*R.card≤U.card together with explicit nonemptiness and proper inclusion; reason: doubling is equivalent to the source inequality and avoids natural-number division
--   - encoding: O(n) queries certifying Eq. (23) → a query family of cardinality at most 8n certifying all inequalities in every consistent graph; reason: Appendix A, printed p.54 (PDF p.55), supplies this uniform explicit budget
-- source:
--   Troy Lee, Finding and Certifying Weighted Minimum Cuts with Cut Queries, STOC 2027 submission #474 (October 2026), Lemma 13 and Eq. (23), printed p.22 (PDF p.23), with §7.2 standing assumptions, printed p.21 (PDF p.22); explicit budget, Appendix A, printed p.54 (PDF p.55); pinned PDF sha256 853e2745e72c36e8e0567917faa6eedd8dfe99b4078a34a70d8d4b81516c372d (citation_basis: published, submission artifact, not an acceptance claim).

import Mathlib
import Definitions.Def_LeeCutCertificates_Certificate_TreePatterns
import Definitions.Def_LeeCutCertificates_Certificate_Terminals

set_option autoImplicit false
open SunMinCut.Cactus

namespace LeeCutCertificates.Certificate

theorem flow_to_half_terminals {n m : ℕ} (hn : 2 ≤ n) (G : Graph n m)
    (hG : Nonnegative G) (hpos : 0 < lam G) (U : Finset (Fin n)) (hU : 2 ≤ U.card) :
    ∃ (R : Finset (Fin n)) (f : Fin n → Fin n → ℝ) (Q : Finset (Finset (Fin n))),
      R.Nonempty ∧ R ⊆ U ∧ R ≠ U ∧ 2 * R.card ≤ U.card ∧ FeasibleFlow G f ∧
      (∀ u ∈ U \ R, divergence f u = lam G / 2) ∧
      (∀ v : Fin n, v ∉ U → divergence f v = 0) ∧
      (∀ v ∈ R, divergence f v ≤ 0) ∧ Q.card ≤ 8 * n ∧
      ∀ (k : ℕ) (H : Graph n k), Nonnegative H → Agrees G H Q →
        ∀ S : Finset (Fin n), Disjoint S R →
          (lam G / 2) * (S ∩ U).card ≤ cutw H S := by sorry

end LeeCutCertificates.Certificate
