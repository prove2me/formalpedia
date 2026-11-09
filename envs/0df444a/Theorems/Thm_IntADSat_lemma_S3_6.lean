-- Prove2me | Theorems.Thm_IntADSat_lemma_S3_6
-- name    : IntADSat.lemma_S3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:51:02.014204+00:00
-- url     : https://prove2.me/theorems/e20df1e8-8c61-40a4-b719-29c346fe172c
-- title:
--   Lemma S3.6 — no sparse kernel vector
-- statement:
--   Let $G\sim G(n,1/2)$ with adjacency matrix $A$ reduced modulo a prime $p$, and let $J$ be any integer with $J\le n/(100\log_2p)$. The probability that there exist $U\subseteq[n]$ with $1\le|U|\le J$ and $0\neq x\in\mathbb F_p^U$ such that
--
--   $$
--   A[[n]\setminus U,\,U]\,x=0
--   $$
--
--   is at most $(n+1)2^{-0.89n}$.
--
--   **Formalization Note** $x$ is a nonzero vector of $\mathbb F_p^n$ supported on $U$, and the kernel equation says $\sum_{j\in U}A_{ij}x_j=0$ for every $i\notin U$.
--
--   Differences from the source:
--   - encoding: 0 ≠ x ∈ 𝔽_p^U → x : Fin n → ZMod p, x ≠ 0, x i = 0 for i ∉ U; reason: same vectors
--   - encoding: integer J ≤ n/(100 log₂ p) → J : ℤ with (J : ℝ) ≤ n/(100 · logb 2 p); reason: same condition
--   - encoding: G ∼ G(n, 1/2) on the labelled vertex set [n] → erProb n (1/2) on SimpleGraph (Fin n) (published Erdős–Rényi product weight at edge probability 1/2); reason: same law: every labelled graph has probability 2^(−n(n−1)/2)
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Lemma S3.6, p.37 (PDF 38)

import Mathlib
import Definitions.Def_UniformADProbes_Trace_algebra
import Definitions.Def_LPCommunity_SBMRecovery_Setting

set_option autoImplicit false
open UniformADProbes.Trace

namespace IntADSat

/-- **Lemma S3.6** (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), p.37 (PDF 38)). For any prime `p` and any integer `J ≤ n/(100 log₂ p)`, the
probability under `G ∼ G(n, 1/2)` that there exist `U ⊆ [n]` with `1 ≤ |U| ≤ J` and `0 ≠ x ∈ 𝔽_p^U`
such that `A[[n] ∖ U, U]x = 0` is at most `(n + 1)2^{−0.89n}`.

**Formalization Note** `x ∈ 𝔽_p^U` is a vector of `𝔽_pⁿ` supported on `U`; `A[[n] ∖ U, U]x = 0` says
`∑_{j ∈ U} A_ij x_j = 0` for every `i ∉ U`, with `A` reduced modulo `p`. -/
theorem lemma_S3_6 (n p : ℕ) (hp : p.Prime) (J : ℤ) (hJ : (J : ℝ) ≤ n / (100 * Real.logb 2 p)) :
    LPCommunity.SBMRecovery.erProb n (1 / 2) (fun G => ∃ U : Finset (Fin n), 1 ≤ U.card ∧ (U.card : ℤ) ≤ J ∧
        ∃ x : Fin n → ZMod p, x ≠ 0 ∧ (∀ i, i ∉ U → x i = 0) ∧
          ∀ i, i ∉ U → ∑ j ∈ U, ((adjacency G i j : ℤ) : ZMod p) * x j = 0) ≤
      ((n : ℝ) + 1) * (2 : ℝ) ^ (-(0.89 : ℝ) * n) := by sorry

end IntADSat
