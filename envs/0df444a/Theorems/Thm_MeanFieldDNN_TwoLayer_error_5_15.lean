-- Prove2me | Theorems.Thm_MeanFieldDNN_TwoLayer_error_5_15
-- name    : MeanFieldDNN.TwoLayer.error_5_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:24:45.852519+00:00
-- url     : https://prove2.me/theorems/a4986e61-29cf-4c22-83b2-646823cc5dc5
-- title:
--   Equation (5.15) — mean squared particle error
-- statement:
--   Fix a solution of (2.6). The error $E_t^{N_2}(c_i,w,u_i,x)$ sums five squared discrepancies: the output weight, first-layer weight, second-layer weight, hidden activation, and hidden preactivation of the $i$th particle and its limiting counterpart. One constant $K$, independent of $N_2$, $i$, $t\in[0,1]$, and $x\in X$, satisfies
--
--   $$\mathbb E[E_t^{N_2}(C_\circ^i,W_0,W_0^{2,i},x)]\le K/N_2.$$
--
--   The expectation uses independent initial vectors $C_\circ$, $W_0$, and $W_0^2$. This estimate is used in the output-rate argument.
--
--   **Formalization Note** The source writes a supremum over $x\in X$; a pointwise bound with the same uniform constant is equivalent for this upper bound.
-- source:
--   Sirignano, Spiliopoulos, Mean Field Analysis of Deep Neural Networks, arXiv:1903.04440v5, p. 20, §5.1, definition of E; p. 24, (5.15)

import Mathlib
import Definitions.Def_MeanFieldDNN_TwoLayer_Model

open MeasureTheory Filter Set
open scoped InnerProductSpace ENNReal

noncomputable section

namespace MeanFieldDNN.TwoLayer

theorem error_5_15 {d : ℕ} (S : Setting d) (L : LimitPaths d)
    (hL : IsLimitSolution S L) :
    ∃ K : ℝ, ∀ (N2 : ℕ), 1 ≤ N2 → ∀ Q : ParticlePaths d N2,
      IsParticleSolution S N2 Q → ∀ i : Fin N2,
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ S.X,
        (∫ cv : Fin N2 → ℝ, ∫ w : E d, ∫ uv : Fin N2 → ℝ,
          errFn S L Q t cv i w uv x
          ∂(Measure.pi fun _ : Fin N2 => S.μW2) ∂S.μW1
          ∂(Measure.pi fun _ : Fin N2 => S.μc)) ≤ K / (N2 : ℝ) := by sorry
end MeanFieldDNN.TwoLayer
