-- Prove2me | Theorems.Thm_LinearMDPRL_Misspec_lemma_C_6
-- name    : LinearMDPRL.Misspec.lemma_C_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:36:36.36763+00:00
-- url     : https://prove2.me/theorems/008dce20-c8bf-46dd-a7fb-e6c24e90982f
-- title:
--   Lemma C.6 (UCB), p. 24 — on 𝔈, Q^k_h(x, a) ≥ Q⋆_h(x, a) − 4H(H + 1 − h)ζ
-- statement:
--   For every value $C\ge0$ of the constant in the event $\mathfrak E$ there is an absolute threshold $c_{\beta,0}>0$ such that, for every $c_\beta\ge c_{\beta,0}$, in the setting of Theorem 3.2 (Assumption B, $d,H,K\ge1$, $p\in(0,1)$, $\lambda=1$, $\beta_k=c_\beta(d\sqrt\iota+\zeta\sqrt{kd})H$), on the event $\mathfrak E$,
--   $$Q^k_h(x,a)\ge Q^\star_h(x,a)-4H(H+1-h)\zeta\qquad\text{for all }(x,a,h,k)\in\mathcal S\times\mathcal A\times[H]\times[K].$$
--
--   Optimism up to a misspecification error: the estimates of Algorithm 1 are upper confidence bounds on $Q^\star$ except for an additive error that grows linearly in $\zeta$ and in the number of remaining steps.
--
--   **Formalization Note** $H+1-h$ is computed in $\mathbb R$; for $h\in[H]$ it is the number of remaining steps. The data are arbitrary apart from $\mathfrak E$, and the threshold $c_{\beta,0}$ is chosen after $C$, as in Lemma C.5.
-- source:
--   arXiv:1907.05388v2, Lemma C.6, p. 24

import Mathlib
import Definitions.Def_LinearMDPRL_Linear_Model
import Definitions.Def_LinearMDPRL_Linear_LSVIUCB
import Definitions.Def_LinearMDPRL_Misspec_ApproxLinearMDP
import Definitions.Def_LinearMDPRL_Misspec_Event

open MeasureTheory ProbabilityTheory Matrix

namespace LinearMDPRL.Misspec

universe u v w

/-- **Lemma C.6** (UCB, p. 24). For every `c_β` at least a threshold `c_β₀` (chosen for the given constant `C` of `𝔈`),
on the event `𝔈`, `Q^k_h(x, a) ≥ LinearMDPRL.Linear.Q⋆_h(x, a) − 4H(H + 1 − h)ζ` for all
`(x, a, h, k) ∈ S × A × [H] × [K]`. -/
theorem lemma_C_6 :
    ∀ C : ℝ, 0 ≤ C → ∃ cβ₀ : ℝ, 0 < cβ₀ ∧ ∀ cβ : ℝ, cβ₀ ≤ cβ →
    ∀ {S : Type u} {A : Type v} [MeasurableSpace S] [Fintype A] [Nonempty A] [LinearOrder A]
      [MeasurableSpace A] [DiscreteMeasurableSpace A] (d H K : ℕ), 1 ≤ d → 1 ≤ H → 1 ≤ K →
    ∀ (M : LinearMDPRL.Linear.EpisodicMDP S A) (φ : S → A → EuclideanSpace ℝ (Fin d)) (ζ : ℝ),
      IsApproxLinearMDP M H d φ ζ →
    ∀ p : ℝ, 0 < p → p < 1 →
    ∀ (xs : ℕ → ℕ → S) (as : ℕ → ℕ → A), goodEvent M φ ζ C cβ p H K xs as →
    ∀ k ∈ Finset.Icc 1 K, ∀ h ∈ Finset.Icc 1 H, ∀ (x : S) (a : A),
      LinearMDPRL.Linear.Qstar M H h x a - 4 * H * ((H : ℝ) + 1 - h) * ζ
        ≤ LinearMDPRL.Linear.lsviQ φ M.r 1 (betaMis cβ ζ d H K p) H xs as k h x a := by sorry

end LinearMDPRL.Misspec
