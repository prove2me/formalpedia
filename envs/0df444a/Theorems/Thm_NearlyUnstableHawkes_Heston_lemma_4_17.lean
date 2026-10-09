-- Prove2me | Theorems.Thm_NearlyUnstableHawkes_Heston_lemma_4_17
-- name    : NearlyUnstableHawkes.Heston.lemma_4_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:35:03.756685+00:00
-- url     : https://prove2.me/theorems/01da4b51-47b1-4435-8656-4250ff28448d
-- title:
--   Lemma 4.17, p. 31 — ∫_0^∞ ∫_x^∞ φ_i(s) ds dx < ∞ for i = 1, 2
-- statement:
--   Let $\phi_1,\phi_2$ satisfy the kernel conditions of Assumption 3; in particular $\phi_i\ge0$ and $\int_0^\infty s(\phi_1(s)+\phi_2(s))\,ds=m<\infty$. Then for $i=1,2$,
--   $$\int_0^{\infty}\int_x^{\infty}\phi_i(s)\,ds\,dx<\infty .$$
--
--   The tails of the kernels are integrable; this controls the tail integrals of $\psi^T$ that appear in $R^T$.
--
--   **Formalization Note** The iterated integral of the nonnegative $\phi_i$ is a lower Lebesgue integral in $[0,\infty]$, so finiteness is the content of the statement. (The paper's proof cites "Assumption 4" for $m<\infty$; that hypothesis is part of Assumption 3.)
-- source:
--   Jaisson and Rosenbaum, Limit theorems for nearly unstable Hawkes processes, arXiv:1310.2033v2, p. 31, Lemma 4.17

import Mathlib
import Definitions.Def_NearlyUnstableHawkes_Heston_Kernel

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace NearlyUnstableHawkes.Heston

/-- Lemma 4.17, p. 31: for `i = 1, 2`, `∫_0^∞ ∫_x^∞ φ_i(s) ds dx < ∞`. -/
theorem lemma_4_17 (φ₁ φ₂ : ℝ → ℝ) (m : ℝ) (hK : KernelAssumption3 φ₁ φ₂ m) :
    (∫⁻ x in Set.Ici (0 : ℝ), ∫⁻ s in Set.Ici x, ENNReal.ofReal (φ₁ s)) < ∞ ∧
      (∫⁻ x in Set.Ici (0 : ℝ), ∫⁻ s in Set.Ici x, ENNReal.ofReal (φ₂ s)) < ∞ := by sorry

end NearlyUnstableHawkes.Heston
