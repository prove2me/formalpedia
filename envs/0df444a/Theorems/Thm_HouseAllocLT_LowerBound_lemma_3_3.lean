-- Prove2me | Theorems.Thm_HouseAllocLT_LowerBound_lemma_3_3
-- name    : HouseAllocLT.LowerBound.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:04:21.574202+00:00
-- url     : https://prove2.me/theorems/fc802c28-4edc-4143-ada4-cb55e9efb603
-- title:
--   Lemma 3.3 — the benchmark and deficiency
-- statement:
--   Let $n\ge1$. For every length vector $\boldsymbol\ell\in[n]^n$, put $Z_h=|\{i:\ell_i\le h\}|$ for $0\le h\le n$, and $\Delta_n=\max_{0\le h\le n}(Z_h-h)$. Every rank-maximal matching at $(P^{\ell_i})_i$ has size $n-\Delta_n$ and its signature, padded through rank $n$, has $n-\Delta_n$ initial ones followed by zeros. Furthermore,
--
--   $$\mathbb E[\Delta_n]\le\sqrt{\frac{n\ln(n+1)}2},\qquad \mathbb E[\nu(G(\mathbf P))]\ge n-\sqrt{\frac{n\ln(n+1)}2}.$$
--
--   For every length vector, the maximum matching size also equals $n-\Delta_n$. Thus the maximum-size and rank-maximal benchmarks agree on these profiles. The expectations use independent uniform list lengths. The maximum-size identity is stated immediately after the italic lemma and proved in Appendix A.1.
--
--   Differences from the source:
--   - encoding: agents, objects and ranks numbered from one → Fin indices numbered from zero; reason: the bijection sends each code index j to the source index j+1
--   - encoding: expectation over independent uniform list lengths → finite sum divided by n^n; reason: the n^n length vectors have equal mass for positive n
--   - encoding: integer maximum of Z_h-h including h=0 → maximum of truncated natural differences; reason: the h=0 term is zero, so replacing negative terms by zero preserves the maximum
-- source:
--   Jinshan Zhang, Nan Zhao, Hao Xu, Meng Xi, Lin Zhao, STOC 2027 submission #174 (October 2026), Lemma 3.3, equation (5), maximum-size identity; proof PDF p.15 (printed p.13), PDF p. 8 (printed p. 6); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/174.pdf

import Definitions.Def_HouseAllocLT_LowerBound_prefixList

open scoped BigOperators ENNReal Topology
open Filter

namespace HouseAllocLT.LowerBound

/-- Lemma 3.3, PDF p.8 (printed p.6), equation (5), and its maximum-size
identity proved in Appendix A.1, PDF p.15. All rank-maximal matchings are covered. -/
theorem lemma_3_3 {n : ℕ} (hn : 1 ≤ n) :
    (∀ (ℓ : Fin n → Fin n) (μ : Assignment n n), RankMaximal (prefixProfile ℓ) μ →
      μ.card = n - deficiency ℓ ∧
      ∀ j : Fin n, rankCount (prefixProfile ℓ) μ j.val =
        if j.val < n - deficiency ℓ then 1 else 0) ∧
    profileAverage (fun ℓ : Fin n → Fin n => (deficiency ℓ : ℝ)) ≤ deviationBound n ∧
    (n : ℝ) - deviationBound n ≤
      profileAverage (fun ℓ : Fin n → Fin n => (maximumSize (prefixProfile ℓ) : ℝ)) ∧
    (∀ ℓ : Fin n → Fin n, maximumSize (prefixProfile ℓ) = n - deficiency ℓ) := by sorry

end HouseAllocLT.LowerBound
