-- Prove2me | Theorems.Thm_LinearMDPRL_Misspec_lemma_C_2
-- name    : LinearMDPRL.Misspec.lemma_C_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:36:03.591997+00:00
-- url     : https://prove2.me/theorems/43d0bdaf-b6cb-4c9b-882e-d30d1746ecc9
-- title:
--   Lemma C.2 (Bound on Weights of Value Functions), p. 21 — ‖w^π_h‖ ≤ 2H√d
-- statement:
--   Under Assumption B, fix a representation $(\mu_h,\theta_h)_{h\in[H]}$ and a measurable policy $\pi$, and let $w^\pi_h=\theta_h+\int V^\pi_{h+1}\,\mathrm d\mu_h$ be the weights of Lemma C.1. Then
--   $$\forall h\in[H],\qquad\|w^\pi_h\|\le2H\sqrt d.$$
--
--   The bound feeds the regularization term $q_1$ in the proof of Lemma C.5.
--
--   **Formalization Note** The action set is finite and nonempty, as in §2. The statement uses the normalization $\big(\sum_i|\mu^{(i)}_h|(\mathcal S)^2\big)^{1/2}\le\sqrt d$ on total variations, which replaces the page's $\|\mu_h(\mathcal S)\|\le\sqrt d$ (see the definition of Assumption B). Under the printed normalization the lemma is false: net masses do not bound $\int V\,\mathrm d\mu_h$.
-- source:
--   arXiv:1907.05388v2, Lemma C.2, p. 21

import Mathlib
import Definitions.Def_LinearMDPRL_Linear_Model
import Definitions.Def_LinearMDPRL_Misspec_ApproxLinearMDP

open MeasureTheory ProbabilityTheory

namespace LinearMDPRL.Misspec

universe u v

/-- **Lemma C.2** (Bound on Weights of Value Functions, p. 21). Under Assumption B, for a fixed
representation `(µ_h, θ_h)_{h ∈ [H]}` and any measurable policy `π`, the weights of Lemma C.1
satisfy `‖w^π_h‖ ≤ 2H√d` for every `h ∈ [H]`. -/
theorem lemma_C_2 {S : Type u} {A : Type v} [MeasurableSpace S] [Fintype A] [Nonempty A] [MeasurableSpace A]
    [DiscreteMeasurableSpace A] (d H : ℕ) (M : LinearMDPRL.Linear.EpisodicMDP S A)
    (φ : S → A → EuclideanSpace ℝ (Fin d)) (ζ : ℝ) (hM : IsApproxLinearMDP M H d φ ζ)
    (mu : ℕ → Fin d → SignedMeasure S) (θ : ℕ → EuclideanSpace ℝ (Fin d))
    (hrep : ∀ h ∈ Finset.Icc 1 H, IsApproxRep M φ ζ h (mu h) (θ h))
    (π : LinearMDPRL.Linear.Policy S A) (hπ : LinearMDPRL.Linear.IsMeasurablePolicy π) :
    ∀ h ∈ Finset.Icc 1 H, ‖repWeight M H π mu θ h‖ ≤ 2 * H * Real.sqrt d := by sorry

end LinearMDPRL.Misspec
