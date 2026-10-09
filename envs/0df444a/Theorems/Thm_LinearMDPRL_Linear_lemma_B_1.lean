-- Prove2me | Theorems.Thm_LinearMDPRL_Linear_lemma_B_1
-- name    : LinearMDPRL.Linear.lemma_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:44:38.30202+00:00
-- url     : https://prove2.me/theorems/9f47167b-29eb-419c-9961-33738f511834
-- title:
--   Lemma B.1, p. 16 — under Assumption A the weights of Q^π satisfy ‖w^π_h‖ ≤ 2H√d
-- statement:
--   Under Assumption A, let $\pi$ be a fixed measurable policy. Then there are weights $(w^\pi_h)_{h\in[H]}$ such that $Q^\pi_h(x,a)=\langle\phi(x,a),w^\pi_h\rangle$ for all $(x,a,h)\in\mathcal S\times\mathcal A\times[H]$ and
--   $$
--   \|w^\pi_h\|\le 2H\sqrt d\qquad\text{for all }h\in[H].
--   $$
--
--   The bound on the weights of true action-value functions is what lets the regularization bias of ridge regression be absorbed into the exploration bonus (Lemma B.4).
--
--   **Formalization Note.** The paper says "let $\{w^\pi_h\}$ be the corresponding weights", which read as "every such family" is false when the features do not span $\mathbb R^d$ (any vector orthogonal to their span can be added). The proof bounds the weights $w^\pi_h=\theta_h+\int V^\pi_{h+1}\,d\boldsymbol\mu_h$ constructed in Proposition 2.3, so the statement asserts the existence of linear weights with the bound; when the features span $\mathbb R^d$ the weights are unique and the two readings coincide. The policy is assumed measurable, and Assumption A is used with the total-variation normalization, without which the lemma is false.
-- source:
--   Jin, Yang, Wang, Jordan, arXiv:1907.05388v2, Lemma B.1, p. 16

import Mathlib
import Definitions.Def_LinearMDPRL_Linear_Model
import Definitions.Def_LinearMDPRL_Linear_LinearMDP

namespace LinearMDPRL.Linear

open MeasureTheory ProbabilityTheory

/-- **Lemma B.1** (Bound on Weights of Value Functions; arXiv:1907.05388v2, p. 16). Under
Assumption A, for any fixed (measurable) policy `π`, the weights `w^π_h` of Proposition 2.3 with
`Q^π_h(x, a) = ⟨φ(x, a), w^π_h⟩` for all `(x, a, h) ∈ S × A × [H]` can be taken with
`‖w^π_h‖ ≤ 2H√d` for every `h ∈ [H]`. -/
theorem lemma_B_1 {S A : Type*} [MeasurableSpace S] [Fintype A] [Nonempty A]
    [MeasurableSpace A] [DiscreteMeasurableSpace A] (H d : ℕ) (M : EpisodicMDP S A)
    (φ : S → A → EuclideanSpace ℝ (Fin d)) (hM : IsLinearMDP M H d φ)
    (π : Policy S A) (hπ : IsMeasurablePolicy π) :
    ∃ w : ℕ → EuclideanSpace ℝ (Fin d), ∀ h ∈ Finset.Icc 1 H,
      (∀ x a, Q M H π h x a = inner ℝ (φ x a) (w h)) ∧ ‖w h‖ ≤ 2 * H * Real.sqrt d := by sorry

end LinearMDPRL.Linear
