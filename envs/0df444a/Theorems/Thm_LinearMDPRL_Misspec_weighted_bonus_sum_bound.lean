-- Prove2me | Theorems.Thm_LinearMDPRL_Misspec_weighted_bonus_sum_bound
-- name    : LinearMDPRL.Misspec.weighted_bonus_sum_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:36:45.782589+00:00
-- url     : https://prove2.me/theorems/f2634b5c-568c-4196-9139-22a15ccb0f22
-- title:
--   (21)–(24), p. 25 — Σ_k β_k Σ_h ‖φ^k_h‖_{(Λ^k_h)^{-1}} ≤ 2c(√(d³H³Tι²) + ζdHT√ι)
-- statement:
--   Let $d,H,K\ge1$, $T=KH$, $p\in(0,1)$, $\iota=\log(2dT/p)$, $\zeta\ge0$ and $c>0$, and set $\beta_k=c\,(d\sqrt\iota+\zeta\sqrt{kd})H$. Let $\phi$ be a feature map with $\|\phi(x,a)\|\le1$, let $(x^k_h,a^k_h)$ be arbitrary data with $\phi^k_h=\phi(x^k_h,a^k_h)$, and $\Lambda^k_h=\sum_{\tau=1}^{k-1}\phi^\tau_h(\phi^\tau_h)^\top+I$. Then
--   $$\sum_{k=1}^K\beta_k\sum_{h=1}^H\sqrt{(\phi^k_h)^\top(\Lambda^k_h)^{-1}\phi^k_h}\le2c\cdot\Big(\sqrt{d^3H^3T\iota^2}+\zeta dHT\sqrt\iota\Big).\qquad(24)$$
--
--   This bounds the accumulated exploration bonuses in the regret decomposition (19). It combines the Cauchy–Schwarz inequality (21), the elliptical potential bound (22) and the estimate (23) of $\sum_k\beta_k^2$.
--
--   **Formalization Note** The statement is deterministic: it holds for every data sequence. $\lambda=1$, as in Theorem 3.2.
-- source:
--   arXiv:1907.05388v2, App. C, proof of Theorem 3.2, (21)–(24), p. 25

import Mathlib
import Definitions.Def_LinearMDPRL_Linear_Model
import Definitions.Def_LinearMDPRL_Linear_LSVIUCB
import Definitions.Def_LinearMDPRL_Misspec_ApproxLinearMDP
import Definitions.Def_LinearMDPRL_Misspec_Event

open MeasureTheory ProbabilityTheory Matrix

namespace LinearMDPRL.Misspec

universe u v w

/-- **(21)–(24)**, App. C, proof of Theorem 3.2 (p. 25). For arbitrary data with `‖φ‖ ≤ 1`, `λ = 1`,
`d, H, K ≥ 1`, `p ∈ (0, 1)`, `ζ ≥ 0`, `c > 0` and `β_k = c (d√ι + ζ√(kd)) H`:
`Σ_{k=1}^K β_k Σ_{h=1}^H √((φ^k_h)^⊤ (Λ^k_h)^{-1} φ^k_h) ≤ 2c (√(d³H³Tι²) + ζ d H T √ι)`,
with `T = KH` and `ι = log(2dT/p)`. -/
theorem weighted_bonus_sum_bound {S : Type u} {A : Type v} (d H K : ℕ) (hd : 1 ≤ d) (hH : 1 ≤ H)
    (hK : 1 ≤ K) (φ : S → A → EuclideanSpace ℝ (Fin d)) (hφ : ∀ x a, ‖φ x a‖ ≤ 1)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (ζ : ℝ) (hζ : 0 ≤ ζ) (c : ℝ) (hc : 0 < c)
    (xs : ℕ → ℕ → S) (as : ℕ → ℕ → A) :
    ∑ k ∈ Finset.Icc 1 K, betaMis c ζ d H K p k *
        ∑ h ∈ Finset.Icc 1 H,
          Real.sqrt (WithLp.ofLp (φ (xs k h) (as k h)) ⬝ᵥ
            (LinearMDPRL.Linear.gram φ 1 xs as k h)⁻¹ *ᵥ WithLp.ofLp (φ (xs k h) (as k h)))
      ≤ 2 * c * (Real.sqrt ((d : ℝ) ^ 3 * (H : ℝ) ^ 3 * ((K : ℝ) * H) * LinearMDPRL.Linear.iota d K H p ^ 2)
          + ζ * d * H * ((K : ℝ) * H) * Real.sqrt (LinearMDPRL.Linear.iota d K H p)) := by sorry

end LinearMDPRL.Misspec
