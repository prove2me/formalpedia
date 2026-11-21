-- Prove2me | Theorems.Thm_NymanBeurling_damped_moebius_iterated_tail_bound
-- name    : NymanBeurling.damped_moebius_iterated_tail_bound
-- status  : Open
-- author  : @ibecca
-- created : 2026-11-21T01:10:49.207783+00:00
-- url     : https://prove2.me/theorems/274ea5c2-a429-46f6-9441-2573eb0de9b5
-- title:
--   Open iterated uniform tail bound for damped Mobius remainder sums
-- statement:
--   Let
--   $$E_{N,\varepsilon}(m)=1+\sum_{d=2}^{N+1}\frac{\mu(d)}{d^\varepsilon}\frac{m\bmod d}{d}.$$
--   For every $\delta>0$, the proposed estimate asks for a coordinate cutoff $H_0\ge0$ and a damping threshold $\varepsilon_0>0$ such that, for every $0<\varepsilon<\varepsilon_0$, there is $N_0$ with
--   $$\sum_{m=H_0+1}^{H}\frac{E_{N,\varepsilon}(m)^2}{m(m+1)}<\delta\qquad(N\ge N_0,\ H\ge0).$$
--   An empty tail sum is zero. The cutoff $H_0$ is chosen before $\varepsilon$, while the truncation threshold $N_0$ may depend on $\varepsilon$; the displayed bound is uniform in the upper coordinate cutoff $H$.
--   This is an **open unconditional assertion** retaining the central analytic difficulty. Together with unconditional finite-coordinate approximation, it implies the damped mean-square approximation frontier. The Riemann hypothesis is not assumed in this target. The cited RH-conditional construction is motivation, not an unconditional proof.
-- source:
--   Open tail-tightness obligation derived from the two successive approximation limits in B. Bagchi, On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation of the Riemann hypothesis (2006), proof of Theorem 2 (i)=>(ii), pp. 140–141, and the sequence identification in the proof of Theorem 1, p. 145, https://arxiv.org/pdf/math/0607733 . That construction assumes RH. This exact tail formulation is a proposed sufficient condition for https://prove2.me/theorems/cf53c71e-758a-4724-897b-66cd8091e51b , not a theorem quoted as unconditional from the source.

import Mathlib

set_option autoImplicit false
open scoped BigOperators

theorem NymanBeurling.damped_moebius_iterated_tail_bound (δ : ℝ) (hδ : 0 < δ) :
    ∃ (H₀ : ℕ) (ε₀ : ℝ), 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ H : ℕ,
        (∑ n ∈ Finset.Ico H₀ H,
          (1 + ∑ k : Fin N,
            ((ArithmeticFunction.moebius (k.val+2) : ℝ) / (k.val+2 : ℝ)^ε) *
              (((n+1) % (k.val+2) : ℕ) : ℝ) / (k.val+2 : ℝ))^2 /
          ((n+1 : ℝ)*(n+2 : ℝ))) < δ := by sorry
