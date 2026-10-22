-- Prove2me | Theorems.Thm_OptimisticPSRL_Concentration_proof_prop5_2_martingale_sum_eq_projection
-- name    : OptimisticPSRL.Concentration.proof_prop5_2_martingale_sum_eq_projection
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T00:40:29.298975+00:00
-- url     : https://prove2.me/theorems/23d5e08b-0ed6-4741-b64c-f2f278bd668d
-- title:
--   Proof of Proposition 5.2, p. 21 — (Σₜ Zₜ)/n = (p̂ − p)ᵀh
-- statement:
--   Let $p\in\Delta^S$, $h\in\mathbb R^S$, and let $c_i$, $y_i=p_i/(p_i+\cdots+p_S)$ be as in the setting. Let $\omega=(\omega_1,\dots,\omega_n)$, $n\ge 1$, be a sequence of trial outcomes each of which has positive probability, $p_{\omega_t}>0$, with empirical vector $\hat p$ and $\hat y_i=\hat p_i/(\hat p_i+\cdots+\hat p_S)$. With $Z_t=\sum_i Z_i(\omega_t)$,
--
--   $$
--   \frac{\sum_{t=1}^nZ_t}{n}=\sum_ic_i\hat p_i-\sum_i\frac{c_ip_i}{p_i+\cdots+p_S}(\hat p_i+\cdots+\hat p_S)=\sum_{i=1}^{S-1}(\hat y_i-y_i)(\hat p_i+\cdots+\hat p_S)c_i=(\hat p-p)^Th.
--   $$
--
--   This display is the first step of the proof of Proposition 5.2: the projection deviation $(\hat p-p)^Th$ is the average of the martingale differences $Z_t$, to which Bernstein's inequality is then applied.
--
--   **Formalization Note** This is the iid reading of the paper's display: the indicator $\mathbb 1(s_{t-1}=s,a_{t-1}=a)$ equals one for every trial and the random count $\tau$ equals $n$. The hypothesis $p_{\omega_t}>0$ holds almost surely and is needed for the middle expression, whose range $i\le S-1$ omits the last state: when a zero-probability state is drawn the last term $(\hat y_S-y_S)\hat p_Sc_S$ need not vanish. The three equalities are stated as a conjunction, in the paper's order. $n\ge1$ is needed because $\hat p$ is an average.
-- source:
--   Agrawal & Jia, Posterior sampling for reinforcement learning: worst-case regret bounds, arXiv:1705.07041v3, p. 21, proof of Proposition 5.2, first and second displays

import Mathlib
import Definitions.Def_OptimisticPSRL_Concentration_Setting

namespace OptimisticPSRL.Concentration

/-- Proof of Proposition 5.2 (Agrawal–Jia, arXiv:1705.07041v3, p. 21, second display), iid
reading: for every outcome sequence `ω` of `n ≥ 1` trials whose outcomes all have positive
probability under `p`,
`(∑_t Z_t)/n = ∑_i c_i p̂_i − ∑_i (c_i p_i/(p_i+⋯+p_S))(p̂_i+⋯+p̂_S)
             = ∑_{i=1}^{S−1} (ŷ_i − y_i)(p̂_i+⋯+p̂_S) c_i = (p̂ − p)ᵀh`. -/
theorem proof_prop5_2_martingale_sum_eq_projection {S n : ℕ} (p h : Fin S → ℝ)
    (hp : IsProbVec p) (hn : 0 < n) (ω : Fin n → Fin S) (hω : ∀ t, 0 < p (ω t)) :
    ((∑ t, ∑ i, Zcoord p h i (ω t)) / n =
        ∑ i, cCoef p h i * phat ω i - ∑ i, cCoef p h i * p i / tail p i * tail (phat ω) i) ∧
      (∑ i, cCoef p h i * phat ω i - ∑ i, cCoef p h i * p i / tail p i * tail (phat ω) i =
        ∑ i ∈ belowLast S, (yRatio (phat ω) i - yRatio p i) * tail (phat ω) i * cCoef p h i) ∧
      (∑ i ∈ belowLast S, (yRatio (phat ω) i - yRatio p i) * tail (phat ω) i * cCoef p h i =
        ∑ i, (phat ω i - p i) * h i) := by sorry

end OptimisticPSRL.Concentration
