-- Prove2me | Theorems.Thm_HiddenCorr_ERM_lemma_1
-- name    : HiddenCorr.ERM.lemma_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:35:10.735052+00:00
-- url     : https://prove2.me/theorems/6002594f-516e-4185-bc97-262440682968
-- title:
--   Lemma 1 — degree lower bounds for the Laplacian energy: $u^\top L^\dagger u\ge\max\{\sum_U 1/\deg,\sum_V 1/\deg\}\ge n^2/m$
-- statement:
--   Let $G=(U\cup V,E)$ be a bipartite graph with $|U|=|V|=n$ and $m=|E|$ edges that admits at least one perfect matching. Let $L$ be its Laplacian and $u$ its bipartite demand vector ($+1$ on $U$, $-1$ on $V$). Then the Laplacian energy $n_{\mathrm{eff}}(G)=u^\top L^\dagger u$ satisfies
--   $$u^\top L^\dagger u\ \ge\ \max\Big\{\sum_{i\in U}\frac1{\deg(i)},\ \sum_{j\in V}\frac1{\deg(j)}\Big\}\ \ge\ \frac{n^2}{m}.$$
--
--   This turns the graph factor $n_{\mathrm{eff}}(G)^{-1/2}$ of the learning guarantees into the explicit factors $\big(\sum 1/\deg\big)^{-1/2}$ and $\sqrt m/n$; it gives the second inequality of Theorem 1.
--
--   Differences from the source:
--   - encoding: [n] and the sides U, V of G; a perfect matching M ∈ M(G) as a bijection U → V → Fin n, U ∪ V as Fin n ⊕ Fin n, E : Finset (Fin n × Fin n), a perfect matching as σ : Equiv.Perm (Fin n) with (i, σ i) ∈ E for all i; reason: Lean convention; the same graphs and matchings
-- source:
--   Chen, Gentile, Kaplan, Koren, Supervised Learning with Hidden Correspondences, STOC 2027 submission (manuscript sha256 d0029978…), p. 15, Lemma 1, Eq. (20) (proof pp. 94–95, App. G.2.1)

import Mathlib
import Definitions.Def_IncrementalER_energy
import Definitions.Def_HiddenCorr_ERM_CandidateGraph

namespace HiddenCorr.ERM

/-- **Lemma 1** (degree lower bounds for the Laplacian energy), p. 15. Let `G` be a bipartite
graph with `n` vertices on each side and edge set `E` (`m = |E|`) that admits at least one perfect
matching. Then its Laplacian energy `uᵀ L† u = n_eff(G)` satisfies
`uᵀL†u ≥ max {∑_{i ∈ U} 1/deg(i), ∑_{j ∈ V} 1/deg(j)} ≥ n²/m`. -/
theorem lemma_1 (n : ℕ) (E : Finset (Fin n × Fin n))
    (hPM : ∃ σ : Equiv.Perm (Fin n), IsPerfectMatching E σ) :
    max (∑ i, 1 / (degU E i : ℝ)) (∑ j, 1 / (degV E j : ℝ)) ≤ neff E ∧
      (n : ℝ) ^ 2 / (E.card : ℝ) ≤ max (∑ i, 1 / (degU E i : ℝ)) (∑ j, 1 / (degV E j : ℝ)) := by sorry

end HiddenCorr.ERM
