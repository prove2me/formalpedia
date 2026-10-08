-- Prove2me | Theorems.Thm_LogGammaPolymer_Variance_lemma_5_4
-- name    : LogGammaPolymer.Variance.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:22:13.036915+00:00
-- url     : https://prove2.me/theorems/99fa4fe4-4e3d-4e2f-b2a1-9b3f9616d7ef
-- title:
--   Lemma 5.4 — for fixed positive weights, Q_{m,n}(ξ_x > 0) is nondecreasing in m
-- statement:
--   For each fixed environment $\omega$ (a configuration of positive weights),
--   $$Q^\omega_{m_1,n}(\xi_x>0)\le Q^\omega_{m_2,n}(\xi_x>0)\qquad\text{for all }0<m_1<m_2\text{ and }n\ge0.$$
--
--   The quenched probability that the polymer path takes its first step along the $x$-axis grows with the horizontal size of the rectangle. The lower-bound proof uses this coupling statement in place of a reversal in a varying rectangle.
--
--   **Formalization Note** A deterministic statement, valid for every weight configuration positive off the origin.
-- source:
--   Seppäläinen, Scaling for a one-dimensional directed polymer with boundary conditions, arXiv:0911.2446v4, Lemma 5.4, p. 28

import Mathlib
import Definitions.Def_LogGammaPolymer_Variance_Paths
import Definitions.Def_LogGammaPolymer_Variance_Environment
open MeasureTheory ProbabilityTheory

namespace LogGammaPolymer.Variance

theorem lemma_5_4 (Y : ℕ × ℕ → ℝ) (hY : ∀ p : ℕ × ℕ, p ≠ (0, 0) → 0 < Y p)
    (m₁ m₂ n : ℕ) (h₁ : 0 < m₁) (h₁₂ : m₁ < m₂) :
    Q Y m₁ n (fun x => 0 < ξx x.1) ≤ Q Y m₂ n (fun x => 0 < ξx x.1) := by sorry

end LogGammaPolymer.Variance
