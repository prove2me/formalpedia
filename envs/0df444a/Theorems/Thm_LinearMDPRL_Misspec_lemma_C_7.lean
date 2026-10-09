-- Prove2me | Theorems.Thm_LinearMDPRL_Misspec_lemma_C_7
-- name    : LinearMDPRL.Misspec.lemma_C_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:36:32.625525+00:00
-- url     : https://prove2.me/theorems/25bfa119-c516-4e65-9199-4a906f750e4c
-- title:
--   Lemma C.7 (Recursive formula), p. 24, with the +4Hζ of its proof — δ^k_h ≤ δ^k_{h+1} + ξ^k_{h+1} + 2β_k‖φ^k_h‖_{(Λ^k_h)^{-1}} + 4Hζ
-- statement:
--   For every value $C\ge0$ of the constant in the event $\mathfrak E$ there is an absolute threshold $c_{\beta,0}>0$ such that, for every $c_\beta\ge c_{\beta,0}$, in the setting of Theorem 3.2 with $\lambda=1$ and $\beta_k=c_\beta(d\sqrt\iota+\zeta\sqrt{kd})H$, along data whose actions are those of Algorithm 1 ($a^k_h=\pi_k(x^k_h,h)$) and on the event $\mathfrak E$, for any $(k,h)\in[K]\times[H]$,
--   $$\delta^k_h\le\delta^k_{h+1}+\xi^k_{h+1}+2\beta_k\sqrt{(\phi^k_h)^\top(\Lambda^k_h)^{-1}\phi^k_h}+4H\zeta,$$
--   where $\delta^k_h=V^k_h(x^k_h)-V^{\pi_k}_h(x^k_h)$, $\xi^k_{h+1}=\mathbb E[\delta^k_{h+1}\mid x^k_h,a^k_h]-\delta^k_{h+1}$ and $\phi^k_h=\phi(x^k_h,a^k_h)$.
--
--   Summed over $h$ and $k$, this reduces the regret to a martingale, the bonuses and a term $4HT\zeta$, which is how it enters (19).
--
--   **Formalization Note** The printed statement omits the term $4H\zeta$. Its own proof derives $Q^k_h-Q^{\pi_k}_h\le\mathbb P_h(V^k_{h+1}-V^{\pi_k}_{h+1})+2\beta_k\sqrt{\cdot}+4H\zeta$, and the printed form does not follow when $(\phi^k_h)^\top(\Lambda^k_h)^{-1}\phi^k_h$ is small; the term is restored here. Theorem 3.2 is unaffected: (19) already carries $\sum_{k,h}4H\zeta=4HT\zeta$. The page writes the noise term as $\zeta^k_{h+1}$; it is renamed $\xi^k_{h+1}$ to avoid a clash with the misspecification level. $\mathbb E[\cdot\mid x^k_h,a^k_h]$ is the integral against $\mathbb P_h(\cdot\mid x^k_h,a^k_h)$ of the fixed function $V^k_{h+1}-V^{\pi_k}_{h+1}$.
-- source:
--   arXiv:1907.05388v2, Lemma C.7, p. 24 (corrected by its proof, p. 24)

import Mathlib
import Definitions.Def_LinearMDPRL_Linear_Model
import Definitions.Def_LinearMDPRL_Linear_LSVIUCB
import Definitions.Def_LinearMDPRL_Misspec_ApproxLinearMDP
import Definitions.Def_LinearMDPRL_Misspec_Event

open MeasureTheory ProbabilityTheory Matrix

namespace LinearMDPRL.Misspec

universe u v w

/-- **Lemma C.7** (Recursive formula, p. 24), with the `+ 4Hζ` that its proof derives. For every `c_β`
at least a threshold `c_β₀` (chosen for the constant `C` of `𝔈`), along data whose actions are those of Algorithm 1, on the event `𝔈`, for all
`(k, h) ∈ [K] × [H]`: `δ^k_h ≤ δ^k_{h+1} + ξ^k_{h+1} + 2β_k √((φ^k_h)^⊤ (Λ^k_h)^{-1} φ^k_h) + 4Hζ`,
where `δ^k_h = LinearMDPRL.Linear.V^k_h(x^k_h) − LinearMDPRL.Linear.V^{π_k}_h(x^k_h)` (`gapAt`) and
`ξ^k_{h+1} = E[δ^k_{h+1} | x^k_h, a^k_h] − δ^k_{h+1}` (`xiNext`; the page writes `ζ^k_{h+1}`). -/
theorem lemma_C_7 :
    ∀ C : ℝ, 0 ≤ C → ∃ cβ₀ : ℝ, 0 < cβ₀ ∧ ∀ cβ : ℝ, cβ₀ ≤ cβ →
    ∀ {S : Type u} {A : Type v} [MeasurableSpace S] [Fintype A] [Nonempty A] [LinearOrder A]
      [MeasurableSpace A] [DiscreteMeasurableSpace A] (d H K : ℕ), 1 ≤ d → 1 ≤ H → 1 ≤ K →
    ∀ (M : LinearMDPRL.Linear.EpisodicMDP S A) (φ : S → A → EuclideanSpace ℝ (Fin d)) (ζ : ℝ),
      IsApproxLinearMDP M H d φ ζ →
    ∀ p : ℝ, 0 < p → p < 1 →
    ∀ (xs : ℕ → ℕ → S) (as : ℕ → ℕ → A),
      (∀ k ∈ Finset.Icc 1 K, ∀ h ∈ Finset.Icc 1 H,
        as k h = LinearMDPRL.Linear.greedy (LinearMDPRL.Linear.lsviQ φ M.r 1 (betaMis cβ ζ d H K p) H xs as k h (xs k h))) →
      goodEvent M φ ζ C cβ p H K xs as →
    ∀ k ∈ Finset.Icc 1 K, ∀ h ∈ Finset.Icc 1 H,
      gapAt M φ 1 (betaMis cβ ζ d H K p) H xs as k h
        ≤ gapAt M φ 1 (betaMis cβ ζ d H K p) H xs as k (h + 1)
          + xiNext M φ 1 (betaMis cβ ζ d H K p) H xs as k h
          + 2 * betaMis cβ ζ d H K p k *
              Real.sqrt (WithLp.ofLp (φ (xs k h) (as k h)) ⬝ᵥ
                (LinearMDPRL.Linear.gram φ 1 xs as k h)⁻¹ *ᵥ WithLp.ofLp (φ (xs k h) (as k h)))
          + 4 * H * ζ := by sorry

end LinearMDPRL.Misspec
