-- Prove2me | Theorems.Thm_LinearMDPRL_Misspec_lemma_C_1
-- name    : LinearMDPRL.Misspec.lemma_C_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:36:17.165586+00:00
-- url     : https://prove2.me/theorems/f5a3e3e6-7f6d-4e94-837d-94fce11f93e0
-- title:
--   Lemma C.1, p. 21 — |Q^π_h(x, a) − ⟨φ(x, a), w^π_h⟩| ≤ 2Hζ for w^π_h = θ_h + ∫V^π_{h+1}dµ_h
-- statement:
--   Let the episodic MDP be $\zeta$-approximately linear (Assumption B) with feature map $\phi$, and fix a representation $(\mu_h,\theta_h)_{h\in[H]}$ satisfying (4) and the normalization. For a measurable policy $\pi$ define $w^\pi_h=\theta_h+\int V^\pi_{h+1}(x')\,\mathrm d\mu_h(x')$. Then for all $(x,a,h)\in\mathcal S\times\mathcal A\times[H]$,
--   $$\big|Q^\pi_h(x,a)-\langle\phi(x,a),w^\pi_h\rangle\big|\le2H\zeta.$$
--
--   This is the misspecified counterpart of the linearity of $Q^\pi$ in a linear MDP (Proposition 2.3): every action-value function is uniformly close to a linear function of the features, with an explicit weight.
--
--   **Formalization Note** The representation is an explicit argument because the weights are defined from it. The action set is finite and nonempty, as in §2. The policy is assumed measurable so that $V^\pi$ is a measurable bounded function and its integrals are meaningful. $\|\cdot\|_{\mathrm{TV}}$ in (4) is the total variation norm.
-- source:
--   arXiv:1907.05388v2, Lemma C.1, p. 21

import Mathlib
import Definitions.Def_LinearMDPRL_Linear_Model
import Definitions.Def_LinearMDPRL_Misspec_ApproxLinearMDP

open MeasureTheory ProbabilityTheory

namespace LinearMDPRL.Misspec

universe u v

/-- **Lemma C.1** (p. 21). For a ζ-approximately linear MDP with a fixed representation
`(µ_h, θ_h)_{h ∈ [H]}` of (4), and any measurable policy `π`, the weights
`w^π_h = θ_h + ∫ LinearMDPRL.Linear.V^π_{h+1}(x′) dµ_h(x′)` satisfy `|LinearMDPRL.Linear.Q^π_h(x, a) − ⟨φ(x, a), w^π_h⟩| ≤ 2Hζ`
for all `(x, a, h) ∈ S × A × [H]`. -/
theorem lemma_C_1 {S : Type u} {A : Type v} [MeasurableSpace S] [Fintype A] [Nonempty A] [MeasurableSpace A]
    [DiscreteMeasurableSpace A] (d H : ℕ) (M : LinearMDPRL.Linear.EpisodicMDP S A)
    (φ : S → A → EuclideanSpace ℝ (Fin d)) (ζ : ℝ) (hM : IsApproxLinearMDP M H d φ ζ)
    (mu : ℕ → Fin d → SignedMeasure S) (θ : ℕ → EuclideanSpace ℝ (Fin d))
    (hrep : ∀ h ∈ Finset.Icc 1 H, IsApproxRep M φ ζ h (mu h) (θ h))
    (π : LinearMDPRL.Linear.Policy S A) (hπ : LinearMDPRL.Linear.IsMeasurablePolicy π) :
    ∀ h ∈ Finset.Icc 1 H, ∀ (x : S) (a : A),
      |LinearMDPRL.Linear.Q M H π h x a - inner ℝ (φ x a) (repWeight M H π mu θ h)| ≤ 2 * H * ζ := by sorry

end LinearMDPRL.Misspec
