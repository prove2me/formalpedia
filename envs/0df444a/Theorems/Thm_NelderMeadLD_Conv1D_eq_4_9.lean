-- Prove2me | Theorems.Thm_NelderMeadLD_Conv1D_eq_4_9
-- name    : NelderMeadLD.Conv1D.eq_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:21:09.687607+00:00
-- url     : https://prove2.me/theorems/6ecd2da4-958b-49c9-a2b0-481ecf3d019d
-- title:
--   (4.9), proof of Theorem 4.1, p. 130 — proximity (4.4) implies |x_min − x₁| ≤ N_NM diam(Δ)
-- statement:
--   Let the parameters satisfy (2.1), let $N_{NM}$ be the constant (4.3), and let $x_{\min}$ be a real number. For every pair $\Delta = (x_1, x_2)$ of reals satisfying the proximity property (4.4),
--   $$x_{\min} \in \operatorname{int}\big(x_2,\ x_1 + N_{NM}(x_1 - x_2)\big],$$
--   one has
--   $$|x_{\min} - x_1| \le N_{NM}\, \operatorname{diam}(\Delta), \qquad \operatorname{diam}(\Delta) = |x_1 - x_2|. \tag{4.9}$$
--
--   In the proof of Theorem 4.1 this converts the proximity property, which holds from the bracketing iteration on, into a distance bound that tends to zero with the diameter.
--
--   **Formalization Note** The statement is about an arbitrary pair; along a run it gives (4.9) at every iteration where (4.4) holds. The proof's display writes the interval with a closing ")", (4.4) with "]"; the closed end, as in (4.4), is used.
-- source:
--   Lagarias, Reeds, Wright & Wright, Convergence properties of the Nelder–Mead simplex method in low dimensions, SIAM J. Optim. 9 (1998), p. 130, proof of Theorem 4.1, (4.9)

import Mathlib
import Definitions.Def_NelderMeadLD_Conv1D_Algorithm

open Filter Topology

namespace NelderMeadLD.Conv1D

theorem eq_4_9 (ρ χ γ σ : ℝ) (hpar : ParamsOK ρ χ γ σ) (xmin : ℝ) :
    ∀ p : ℝ × ℝ, Proximity ρ χ γ xmin p → |xmin - p.1| ≤ NNM ρ χ γ * diam p := by sorry

end NelderMeadLD.Conv1D
