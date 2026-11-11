-- Prove2me | Theorems.Thm_LogitRankDistill_lemma_5_9
-- name    : LogitRankDistill.lemma_5_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:59:34.642301+00:00
-- url     : https://prove2.me/theorems/cfa7f480-272a-4a6d-8bf3-92096bd7aa6e
-- title:
--   Lemma 5.9 — per-step total-variation errors of an autoregressive sampler add up
-- statement:
--   Let $M$ be a distribution on $\Sigma^T$ and, for each $t\in[T]$, let $G_t:\Sigma^{t-1}\to\Delta(\Sigma)$ be a deterministic map with
--   $$\mathbb E_{y_{1:t-1}\sim M}\big[D_{TV}\big(G_t(y_{1:t-1}),M(y_t=\cdot\mid y_{1:t-1})\big)\big]\le\varepsilon_t,\qquad\varepsilon_t\ge0 .$$
--   Let $M_G$ be the law that samples $y_t\sim G_t(y_{1:t-1})$ for $t=1,\dots,T$. Then
--   $$D_{TV}(M,M_G)\le\sum_{t=1}^T\varepsilon_t .$$
--   It turns the per-step guarantee (32) into the total-variation bound of Theorem 5.11.
--
--   **Formalization Note.** The maps $G_t$ are one function `G` on histories ($G_t$ is its restriction to $\Sigma^{t-1}$); each $G(h)$ with $|h|<T$ is a probability vector. $M_G(x)=\prod_{j}G(x_{1:j})(x_{j+1})$ (positions 0-based). The expectation is $\sum_xM(x)\,g(x)$.
--
--   Differences from the source:
--   - encoding: a family of maps G_t : Σ^{t−1} → Δ(Σ), t ∈ [T] → one function G on all histories, a probability vector on histories of length < T; reason: families on the disjoint sets Σ^{t−1} and single functions on their union correspond one to one; same instances
-- source:
--   Golowich, Liu, Shetty, Provably Distilling from Modern Language Models via Low Logit Rank, manuscript of November 3, 2026 (arXiv:2512.09892; sha256 2ce0606e…), p. 29, Lemma 5.9

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_TVDist
import Definitions.Def_LogitRankDistill_Models
import Definitions.Def_LogitRankDistill_Algorithms

namespace LogitRankDistill

/-- **Lemma 5.9** (p. 29): if for each `t ∈ [T]` the deterministic map `G_t : Σ^{t−1} → Δ(Σ)`
satisfies `E_{y_{1:t−1} ∼ M}[D_TV(G_t(y_{1:t−1}), M(y_t = · | y_{1:t−1}))] ≤ ε_t` with `ε_t ≥ 0`,
then the law `M_G` sampling `y_t ∼ G_t(y_{1:t−1})` for `t = 1, …, T` satisfies
`D_TV(M, M_G) ≤ ∑_{t=1}^T ε_t`. The maps are one function `G` on histories (`G_t = G` on
`Σ^{t−1}`); position `j` (0-based) of `x` is `y_{j+1}`. -/
theorem lemma_5_9 {Tok : Type*} [Fintype Tok] [DecidableEq Tok] {T : ℕ}
    (M : PMF (Fin T → Tok)) (G : List Tok → Tok → ℝ)
    (hG : ∀ h : List Tok, h.length < T → (∀ y, 0 ≤ G h y) ∧ ∑ y, G h y = 1)
    (ε : ℕ → ℝ) (hε : ∀ t, 0 ≤ ε t)
    (hstep : ∀ t, 1 ≤ t → t ≤ T →
      expect M (fun x => IsingLTL.BeliefProp.tvDist (G (pre x (t - 1)))
        (condProb M (pre x (t - 1)))) ≤ ε t) :
    IsingLTL.BeliefProp.tvDist (fun x : Fin T → Tok => (M x).toReal)
        (fun x => ∏ j : Fin T, G (pre x j) (x j)) ≤ ∑ t ∈ Finset.Icc 1 T, ε t := by sorry

end LogitRankDistill
