-- Prove2me | Theorems.Thm_LinearMDPRL_Linear_lemma_B_6
-- name    : LinearMDPRL.Linear.lemma_B_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:46:14.559695+00:00
-- url     : https://prove2.me/theorems/605ee348-4cc6-43df-8a34-54b701b623ec
-- title:
--   Lemma B.6 (Recursive formula), p. 19 — on 𝔈, δ^k_h ≤ δ^k_{h+1} + ζ^k_{h+1} + 2β‖φ^k_h‖_{(Λ^k_h)^{-1}}
-- statement:
--   Under the setting of Theorem 3.1, for an absolute constant $c_\beta>0$ as in Lemma B.4 and data whose actions are those of Algorithm 1 ($a^k_h=\arg\max_aQ^k_h(x^k_h,a)$), let
--   $$
--   \delta^k_h=V^k_h(x^k_h)-V^{\pi_k}_h(x^k_h),\qquad \zeta^k_{h+1}=\mathbb E\big[\delta^k_{h+1}\mid x^k_h,a^k_h\big]-\delta^k_{h+1},
--   $$
--   where $\pi_k$ is the greedy policy of episode $k$. Then on the event $\mathfrak E$ of Lemma B.3, for any $(k,h)\in[K]\times[H]$,
--   $$
--   \delta^k_h\le\delta^k_{h+1}+\zeta^k_{h+1}+2\beta\sqrt{(\phi^k_h)^\top(\Lambda^k_h)^{-1}\phi^k_h}.
--   $$
--
--   Summed over $h$ and $k$, this recursion bounds the regret by a martingale term plus the sum of the exploration bonuses along the trajectories.
--
--   **Formalization Note.** Within episode $k$ the functions $V^k_{h+1}$ and $V^{\pi_k}_{h+1}$ are fixed, so $\mathbb E[\delta^k_{h+1}\mid x^k_h,a^k_h]$ is the integral $\int(V^k_{h+1}-V^{\pi_k}_{h+1})\,d\mathbb P_h(\cdot\mid x^k_h,a^k_h)$; that is how it is written. As in Lemma B.4, $c_\beta$ is chosen after $C$. $\delta^k_{H+1}=0$ because both value functions vanish at step $H+1$.
-- source:
--   Jin, Yang, Wang, Jordan, arXiv:1907.05388v2, Lemma B.6, p. 19

import Mathlib
import Definitions.Def_LinearMDPRL_Linear_Model
import Definitions.Def_LinearMDPRL_Linear_LSVIUCB
import Definitions.Def_LinearMDPRL_Linear_LinearMDP
import Definitions.Def_LinearMDPRL_Linear_ProofObjects

namespace LinearMDPRL.Linear

open MeasureTheory ProbabilityTheory Matrix

/-- **Lemma B.6** (Recursive formula; arXiv:1907.05388v2, p. 19). Under the setting of Theorem 3.1,
for the `c_β` of Lemma B.4 and data `xs`, `as` whose actions are those of
Algorithm 1, let `δ^k_h = V^k_h(x^k_h) − V^{π_k}_h(x^k_h)` and
`ζ^k_{h+1} = E[δ^k_{h+1} | x^k_h, a^k_h] − δ^k_{h+1}`, where
`E[δ^k_{h+1} | x^k_h, a^k_h] = ∫ (V^k_{h+1} − V^{π_k}_{h+1}) dP_h(· | x^k_h, a^k_h)`. Then on the event
`𝔈`, for any `(k, h) ∈ [K] × [H]`,
`δ^k_h ≤ δ^k_{h+1} + ζ^k_{h+1} + 2β √((φ^k_h)^⊤ (Λ^k_h)^{-1} φ^k_h)`. -/
theorem lemma_B_6 :
    ∀ C : ℝ, 0 ≤ C → ∃ cβ : ℝ, 0 < cβ ∧
      ∀ {S A : Type} [MeasurableSpace S] [Fintype A] [Nonempty A] [LinearOrder A]
        [MeasurableSpace A] [DiscreteMeasurableSpace A] (d H K : ℕ), 1 ≤ d → 1 ≤ H → 1 ≤ K →
      ∀ (M : EpisodicMDP S A) (φ : S → A → EuclideanSpace ℝ (Fin d)), IsLinearMDP M H d φ →
      ∀ p : ℝ, 0 < p → p < 1 →
      ∀ (xs : ℕ → ℕ → S) (as : ℕ → ℕ → A),
        (∀ k ∈ Finset.Icc 1 K, ∀ h ∈ Finset.Icc 1 H,
          as k h = greedy (lsviQ φ M.r 1 (fun _ => cβ * d * H * Real.sqrt (iota d K H p)) H
            xs as k h (xs k h))) →
        goodEvent M φ C cβ p H K xs as →
      ∀ k ∈ Finset.Icc 1 K, ∀ h ∈ Finset.Icc 1 H,
        let β : ℕ → ℝ := fun _ => cβ * d * H * Real.sqrt (iota d K H p)
        let πk : Policy S A := greedyPolicy φ M.r 1 β H xs as k
        let δ : ℕ → ℝ := fun i => lsviV φ M.r 1 β H xs as k i (xs k i) - V M H πk i (xs k i)
        let ζ : ℝ := (∫ y, (lsviV φ M.r 1 β H xs as k (h + 1) y - V M H πk (h + 1) y)
            ∂(M.P h (xs k h, as k h))) - δ (h + 1)
        δ h ≤ δ (h + 1) + ζ + 2 * β k *
          Real.sqrt (WithLp.ofLp (φ (xs k h) (as k h)) ⬝ᵥ
            ((gram φ 1 xs as k h)⁻¹ *ᵥ WithLp.ofLp (φ (xs k h) (as k h)))) := by sorry

end LinearMDPRL.Linear
