-- Prove2me | Theorems.Thm_LinearMDPRL_Linear_proposition_2_3
-- name    : LinearMDPRL.Linear.proposition_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:45:06.119329+00:00
-- url     : https://prove2.me/theorems/36053caa-a497-4c88-987f-eecdc5331b4a
-- title:
--   Proposition 2.3, p. 6 — in a linear MDP, Q^π_h(x, a) = ⟨φ(x, a), w^π_h⟩ for every policy π
-- statement:
--   Let $\mathrm{MDP}(\mathcal S,\mathcal A,H,\mathbb P,r)$ be a linear MDP with feature map $\phi:\mathcal S\times\mathcal A\to\mathbb R^d$ (Assumption A). Then for every measurable policy $\pi$ there exist weights $(w^\pi_h)_{h\in[H]}\subset\mathbb R^d$ such that
--   $$
--   Q^\pi_h(x,a)=\langle\phi(x,a),w^\pi_h\rangle\qquad\text{for all }(x,a,h)\in\mathcal S\times\mathcal A\times[H].
--   $$
--
--   This is the structural property that motivates linear function approximation in this model: whatever the policy, its action-value function lies in the $d$-dimensional span of the features.
--
--   **Formalization Note.** The policy is required to be measurable, so that $V^\pi_{h+1}$ is measurable and its integrals against the transition kernels and the signed measures $\mu_h^{(i)}$ are meaningful. Assumption A is used with the total-variation normalization (see the definition `LinearMDP`).
-- source:
--   Jin, Yang, Wang, Jordan, arXiv:1907.05388v2, Proposition 2.3, p. 6 (proof in App. A, p. 15)

import Mathlib
import Definitions.Def_LinearMDPRL_Linear_Model
import Definitions.Def_LinearMDPRL_Linear_LinearMDP

namespace LinearMDPRL.Linear

open MeasureTheory ProbabilityTheory

/-- **Proposition 2.3** (arXiv:1907.05388v2, p. 6; proof p. 15). For a linear MDP and any
(measurable) policy `π` there are weights `(w^π_h)_{h ∈ [H]}` such that
`Q^π_h(x, a) = ⟨φ(x, a), w^π_h⟩` for all `(x, a, h) ∈ S × A × [H]`. -/
theorem proposition_2_3 {S A : Type*} [MeasurableSpace S] [Fintype A] [Nonempty A]
    [MeasurableSpace A] [DiscreteMeasurableSpace A] (H d : ℕ) (M : EpisodicMDP S A)
    (φ : S → A → EuclideanSpace ℝ (Fin d)) (hM : IsLinearMDP M H d φ)
    (π : Policy S A) (hπ : IsMeasurablePolicy π) :
    ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
      ∀ h ∈ Finset.Icc 1 H, ∀ x a, Q M H π h x a = inner ℝ (φ x a) (w h) := by sorry

end LinearMDPRL.Linear
