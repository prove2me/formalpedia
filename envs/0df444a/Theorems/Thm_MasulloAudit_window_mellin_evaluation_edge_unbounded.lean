-- Prove2me | Theorems.Thm_MasulloAudit_window_mellin_evaluation_edge_unbounded
-- name    : MasulloAudit.window_mellin_evaluation_edge_unbounded
-- status  : Proved
-- author  : @deleted
-- created : 2026-11-21T00:27:50.460178+00:00
-- url     : https://prove2.me/theorems/61f5a90e-910c-4c8d-9c4a-d7ab8702ab78
-- title:
--   At the edge $|\operatorname{Re}z|=\alpha$ Mellin evaluation is unbounded on the window space
-- statement:
--   Let $\alpha>0$ and $c\in\mathbf R$ with $|c|=\alpha$, the edge of the window. Then
--
--   $$
--   \int_{\mathbf R}e^{2cu-2\alpha|u|}\,du=\infty,
--   $$
--
--   and the evaluation functional is unbounded on $L^2(\mathbf R,e^{2\alpha|u|}du)$. There are nonnegative measurable $g_n$ with $\int g_n^2e^{2\alpha|u|}\,du=1$ and $\int g_n(u)e^{cu}\,du\to\infty$.
--
--   Together with `MasulloAudit.window_mellin_evaluation_bounded`, this shows that Mellin evaluation at $z$ is continuous on the window space of Masullo's draft exactly for $|\operatorname{Re}z|<\alpha$. So the window is an open strip, matching the draft's restriction to zeros in the interior of $\tfrac12+I$ (Theorem 12.5.1.1). At $s=0$ the edge zeros are not seen; the draft's capped edge multiplicities for $s>0$ concern Sobolev weights not covered here.
--
--   **Formalization Note.** The weight is $e^{2\alpha|u|}$ (Sobolev degree $0$). Integrals are lower Lebesgue integrals.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, (1.8.2.2) p. 44, Def. 9.2.2.1, Thm 10.4.2.8.

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Topology

namespace MasulloAudit

/-- Sharpness of the window Mellin evaluation at the edge `|c| = α`: the weight
`e^{2cu − 2α|u|}` is not integrable (its lower integral is `∞`), and the functional
`g ↦ ∫ g(u) e^{cu} du` is unbounded on `L²(ℝ, e^{2α|u|} du)`: there are nonnegative measurable
`g n` of unit weighted `L²` norm with `∫ g n · e^{cu} → ∞`. -/
theorem window_mellin_evaluation_edge_unbounded (α : ℝ) (hα : 0 < α) (c : ℝ) (hc : |c| = α) :
    (∫⁻ u : ℝ, ENNReal.ofReal (Real.exp (2 * c * u - 2 * α * |u|))) = ⊤ ∧
    ∃ g : ℕ → ℝ → ℝ, (∀ n, Measurable (g n)) ∧ (∀ n u, 0 ≤ g n u) ∧
      (∀ n, (∫⁻ u : ℝ, ENNReal.ofReal (g n u ^ 2 * Real.exp (2 * α * |u|))) = 1) ∧
      Tendsto (fun n => ∫⁻ u : ℝ, ENNReal.ofReal (g n u * Real.exp (c * u))) atTop (𝓝 ⊤) := by sorry

end MasulloAudit
