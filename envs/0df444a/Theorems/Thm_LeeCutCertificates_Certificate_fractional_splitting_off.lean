-- Prove2me | Theorems.Thm_LeeCutCertificates_Certificate_fractional_splitting_off
-- name    : LeeCutCertificates.Certificate.fractional_splitting_off
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:47:28.136548+00:00
-- url     : https://prove2.me/theorems/608344b1-6e3e-4dfc-8981-6f7d14852c9b
-- title:
--   Lemma 12 — Fractional splitting off
-- statement:
--   Let $G$ be a nonnegatively weighted undirected graph on $n\ge2$ vertices, and put $\lambda=\lambda(G)>0$, as stipulated throughout §7.2. Let $U\subseteq V$ be any subset. A shore is $U$-separating when both sides contain a terminal of $U$. Suppose $c_G(S)\ge\lambda$ for every such shore. There is a nonnegative weighted graph $J$ on the same vertices, with zero pair capacity whenever either endpoint lies outside $U$, satisfying
--
--   $$c_J(S)\le c_G(S)\quad\text{for every }S\subseteq V,$$
--   $$c_J(S)\ge\lambda\quad\text{for every }U\text{-separating }S.$$
--
--   This is fractional splitting off for arbitrary real capacities with cut domination. Both inequalities are conclusions about the constructed graph, which is existentially supplied by the theorem.
--
--   **Formalization Note** The standing positive value is the original graph's global minimum-cut value. There is no integrality, Eulerianity, regular-degree, or lower bound on $|U|$. Empty and singleton $U$ are included. The explicitly printed terminal lower-bound hypothesis is retained, although the global minimum-cut convention already implies it.
--
--   Differences from the source:
--   - encoding: finite labelled vertices with symmetric nonnegative real pair weights → Fin n with n≥2 and arbitrary nonnegative real edge records, aggregating parallel records and ignoring loops; all competitors have arbitrary independent record counts and endpoints; reason: every source weighting has an edge-record representation and all cuts and flows use its aggregate pair capacities; no support or connectivity restriction is added
-- source:
--   Troy Lee, Finding and Certifying Weighted Minimum Cuts with Cut Queries, STOC 2027 submission #474 (October 2026), Lemma 12 and §7.2 standing assumptions, printed p.21 (PDF p.22), proof continuing on printed p.22 (PDF p.23); pinned PDF sha256 853e2745e72c36e8e0567917faa6eedd8dfe99b4078a34a70d8d4b81516c372d (citation_basis: published, submission artifact, not an acceptance claim).

import Mathlib
import Definitions.Def_LeeCutCertificates_Certificate_TreePatterns
import Definitions.Def_LeeCutCertificates_Certificate_Terminals

set_option autoImplicit false
open SunMinCut.Cactus

namespace LeeCutCertificates.Certificate

theorem fractional_splitting_off {n m : ℕ} (hn : 2 ≤ n) (G : Graph n m)
    (hG : Nonnegative G) (hpos : 0 < lam G) (U : Finset (Fin n))
    (hU : ∀ S : Finset (Fin n), Separates U S → lam G ≤ cutw G S) :
    ∃ (k : ℕ) (J : Graph n k), Nonnegative J ∧
      (∀ u v : Fin n, u ∉ U ∨ v ∉ U → pairWeight J u v = 0) ∧
      (∀ S : Finset (Fin n), cutw J S ≤ cutw G S) ∧
      (∀ S : Finset (Fin n), Separates U S → lam G ≤ cutw J S) := by sorry

end LeeCutCertificates.Certificate
