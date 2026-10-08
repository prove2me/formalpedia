-- Prove2me | Theorems.Thm_KellyReversibility_Allocation_multiplier_choice
-- name    : KellyReversibility.Allocation.multiplier_choice
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T03:08:22.558136+00:00
-- url     : https://prove2.me/theorems/8bc3ef13-7aef-410e-8edc-dd9221d14337
-- title:
--   Proof of Theorem 4.1, p. 97 — the multiplier 1/√y = (F − ∑ a_k f_k)/∑ √(a_k f_k) meets (4.2)
-- statement:
--   Let $J \ge 1$, $a_j > 0$, $f_j > 0$ for every $j$, and $F > \sum_k a_k f_k$. Define
--   $$y = \left(\frac{\sum_k \sqrt{a_k f_k}}{F - \sum_k a_k f_k}\right)^{2}.$$
--   Then $y > 0$,
--   $$\frac{1}{\sqrt y} = \frac{F - \sum_k a_k f_k}{\sum_k \sqrt{a_k f_k}},$$
--   the Lagrangian minimizer $\phi^y_j = a_j + \sqrt{a_j/(y f_j)}$ coincides with the allocation of Theorem 4.1,
--   $$a_j + \sqrt{\frac{a_j}{y f_j}} = a_j + \frac{\sqrt{a_j f_j}}{\sum_k \sqrt{a_k f_k}}\cdot\frac{F - \sum_k a_k f_k}{f_j} \quad\text{for every } j,$$
--   and it satisfies the cost constraint (4.2): $\sum_j f_j \phi^y_j = F$.
--
--   This is the step that chooses the multiplier so that the minimizer of the Lagrangian is feasible.
--
--   **Formalization Note** The hypotheses $J \ge 1$ and $F > \sum_k a_k f_k$ are implicit in the book; they make $y$ well defined and positive.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 97, proof of Theorem 4.1 (substitution in constraint (4.2))

import Mathlib
import Definitions.Def_KellyReversibility_Allocation_CapacityAllocation

namespace KellyReversibility.Allocation

theorem multiplier_choice {J : ℕ} (hJ : 0 < J) (a f : Fin J → ℝ) (F : ℝ)
    (ha : ∀ j, 0 < a j) (hf : ∀ j, 0 < f j) (hF : ∑ k, a k * f k < F) :
    let y : ℝ := ((∑ k, Real.sqrt (a k * f k)) / (F - ∑ k, a k * f k)) ^ 2
    0 < y ∧ 1 / Real.sqrt y = (F - ∑ k, a k * f k) / ∑ k, Real.sqrt (a k * f k) ∧
      (∀ j, a j + Real.sqrt (a j / (y * f j)) = optimalAllocation a f F j) ∧
      ∑ j, f j * (a j + Real.sqrt (a j / (y * f j))) = F := by sorry

end KellyReversibility.Allocation
