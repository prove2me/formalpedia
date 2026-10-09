-- Prove2me | Theorems.Thm_LinearMDPRL_Linear_bonus_sum_bound
-- name    : LinearMDPRL.Linear.bonus_sum_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:45:25.212592+00:00
-- url     : https://prove2.me/theorems/1864334e-cdf1-4d5b-98a3-6cce7210e9d6
-- title:
--   (17)–(18), p. 20 — Σ_k (φ^k_h)^⊤(Λ^k_h)^{-1}φ^k_h ≤ 2d log(1 + K) ≤ 2dι and Σ_k Σ_h √((φ^k_h)^⊤(Λ^k_h)^{-1}φ^k_h) ≤ H√(2dKι)
-- statement:
--   Consider any data of $K$ episodes of LSVI-UCB with $\lambda=1$ and features with $\|\phi(x,a)\|\le1$, and write $\phi^k_h=\phi(x^k_h,a^k_h)$ and $\Lambda^k_h=\sum_{\tau=1}^{k-1}\phi^\tau_h(\phi^\tau_h)^\top+I$. Let $d,H,K\ge1$, $p\in(0,1)$ and $\iota=\log(2dT/p)$ with $T=KH$. Then:
--
--   1. (17) for every $h\in[H]$,
--   $$
--   \sum_{k=1}^K(\phi^k_h)^\top(\Lambda^k_h)^{-1}\phi^k_h\le 2d\log\Big(\frac{\lambda+K}{\lambda}\Big)=2d\log(1+K)\le 2d\iota ;
--   $$
--   2. (18)
--   $$
--   \sum_{k=1}^K\sum_{h=1}^H\sqrt{(\phi^k_h)^\top(\Lambda^k_h)^{-1}\phi^k_h}\le H\cdot\sqrt{2dK\iota}.
--   $$
--
--   This bounds the total exploration bonus collected along the played trajectories, the second term of the regret decomposition (15).
--
--   **Formalization Note.** The page writes $\log((\lambda+k)/\lambda)$ in (17) with a lower-case $k$; the sum runs to $K$ and the bound is $\log((\lambda+K)/\lambda)$, which equals $\log(1+K)$ at $\lambda=1$. This is a reading of a typo, not a change of the statement.
-- source:
--   Jin, Yang, Wang, Jordan, arXiv:1907.05388v2, App. B, proof of Theorem 3.1, equations (17)–(18), p. 20

import Mathlib
import Definitions.Def_LinearMDPRL_Linear_LSVIUCB

namespace LinearMDPRL.Linear

open Matrix

/-- **(17)–(18)** (App. B, proof of Theorem 3.1, arXiv:1907.05388v2, p. 20). For any observed data
of `K` episodes, with `λ = 1`, `‖φ‖ ≤ 1`, `φ^k_h = φ(x^k_h, a^k_h)` and `Λ^k_h` the Gram matrix of
Algorithm 1, `ι = log(2dT/p)`, `T = KH`:

1. (17) for every `h ∈ [H]`,
   `Σ_{k=1}^K (φ^k_h)^⊤ (Λ^k_h)^{-1} φ^k_h ≤ 2d log((λ + K)/λ) = 2d log(1 + K) ≤ 2dι`;
2. (18) `Σ_{k=1}^K Σ_{h=1}^H √((φ^k_h)^⊤ (Λ^k_h)^{-1} φ^k_h) ≤ H √(2dKι)`. -/
theorem bonus_sum_bound {S A : Type*} {d : ℕ} (φ : S → A → EuclideanSpace ℝ (Fin d))
    (hφ : ∀ x a, ‖φ x a‖ ≤ 1) (H K : ℕ) (hd : 1 ≤ d) (hH : 1 ≤ H) (hK : 1 ≤ K)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (xs : ℕ → ℕ → S) (as : ℕ → ℕ → A) :
    (∀ h ∈ Finset.Icc 1 H,
      ∑ k ∈ Finset.Icc 1 K,
          WithLp.ofLp (φ (xs k h) (as k h)) ⬝ᵥ
            ((gram φ 1 xs as k h)⁻¹ *ᵥ WithLp.ofLp (φ (xs k h) (as k h)))
        ≤ 2 * d * Real.log (1 + K) ∧
      2 * d * Real.log (1 + K) ≤ 2 * d * iota d K H p) ∧
    ∑ k ∈ Finset.Icc 1 K, ∑ h ∈ Finset.Icc 1 H,
        Real.sqrt (WithLp.ofLp (φ (xs k h) (as k h)) ⬝ᵥ
          ((gram φ 1 xs as k h)⁻¹ *ᵥ WithLp.ofLp (φ (xs k h) (as k h))))
      ≤ H * Real.sqrt (2 * d * K * iota d K H p) := by sorry

end LinearMDPRL.Linear
