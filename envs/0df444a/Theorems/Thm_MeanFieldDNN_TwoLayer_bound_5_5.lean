-- Prove2me | Theorems.Thm_MeanFieldDNN_TwoLayer_bound_5_5
-- name    : MeanFieldDNN.TwoLayer.bound_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:24:45.44341+00:00
-- url     : https://prove2.me/theorems/80b58fbf-9358-475d-9f86-033c3983b85f
-- title:
--   Equation (5.5) — uniform particle bounds
-- statement:
--   For every positive $N_2$, every solution of the finite particle system (5.1), every $t\in[0,1]$ and $x\in X$, a single constant $K$ bounds the magnitudes of the particle output, output weight, second-layer weight, interaction term, and first-layer weight:
--
--   $$\max\{|g_t^{N_2}(x)|,|C_t^i|,|W_t^{2,i}|,|V_t^{N_2}|,\|W_t^1\|\}\le K.$$
--
--   The bound is uniform in $N_2$, the particle index, time, and supported initial values. It supplies control of all evolving components used in later error estimates.
--
--   **Formalization Note** The source states the bound for random initial values. The Lean theorem quantifies over every point of their compact full-measure supports, a disclosed supported-value reading.
-- source:
--   Sirignano, Spiliopoulos, Mean Field Analysis of Deep Neural Networks, arXiv:1903.04440v5, p. 20, (5.5)

import Mathlib
import Definitions.Def_MeanFieldDNN_TwoLayer_Model

open MeasureTheory Filter Set
open scoped InnerProductSpace ENNReal

noncomputable section

namespace MeanFieldDNN.TwoLayer

theorem bound_5_5 {d : ℕ} (S : Setting d) :
    ∃ K : ℝ, ∀ (N2 : ℕ), 1 ≤ N2 → ∀ Q : ParticlePaths d N2,
      IsParticleSolution S N2 Q → ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ S.X,
      ∀ cv : Fin N2 → ℝ, (∀ i, cv i ∈ S.Cset) →
      ∀ w ∈ S.W1set, ∀ uv : Fin N2 → ℝ, (∀ i, uv i ∈ S.W2set) → ∀ i,
        max (|partG S Q t cv x|)
          (max (|Q.Cp t cv i|)
            (max (|Q.W2p t cv i w uv|)
              (max (|partV S Q t cv w uv x|) ‖Q.W1p t cv w uv‖))) ≤ K := by sorry

end MeanFieldDNN.TwoLayer
