-- Prove2me | Theorems.Thm_Fundraising_Competition_eq_S8
-- name    : Fundraising.Competition.eq_S8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:03:13.583811+00:00
-- url     : https://prove2.me/theorems/59d796b8-c649-48c6-a389-5a46f959017c
-- title:
--   (S8), proof of Proposition 1, p. S12 — second derivative of log Σ_a w^a θ^{J_a}(s) in s_i is at most 1/4 − e^{s_i}/(1+e^{s_i})²
-- statement:
--   Let $(s;x)$ be a profile with every effort $x_j \in [0,1]$ and let $i$ be an HO. As a function of HO $i$'s base utility $t = s_i$ (the other coordinates fixed), the mixture of MNL shares $\Sigma_i(t) = \sum_{a \in A_i} w^a_i\, \theta^{J_a}_i(s_{-i}, t)$ satisfies, at $t = s_i$,
--   $$\frac{\partial^2 \log \Sigma_i(t)}{\partial t^2} \le \frac14 - \frac{e^{s_i}}{(1+e^{s_i})^2}.$$
--
--   The bound says that the logarithm of a probability mixture of logit shares is at most "$1/4 - \theta(1-\theta)$"-convex; combined with Assumption 1 it makes the unit performance per donor contacted log-concave in the HO's own base utility.
--
--   **Formalization Note.** The derivative is Mathlib's `deriv` of the function $t \mapsto \log \Sigma_i(s_{-i}, t)$, which is smooth and positive (the weights $w^a_i$ are nonnegative and sum to one for efforts in $[0,1]$). The paper drops the index $i$ in this display.
-- source:
--   Aflaki, Pedraza-Martinez, Competition and Collaboration on Fundraising for Short-Term Disaster Response: The Impact on Earmarking and Performance, SSRN 3705595 (version of December 2022), p. S12 (PDF 45), proof of Proposition 1, (S8)

import Mathlib
import Definitions.Def_Fundraising_Competition_Setting

namespace Fundraising.Competition

theorem eq_S8 {n : ℕ} (s x : Fin n → ℝ) (hx : ∀ j, x j ∈ Set.Icc (0 : ℝ) 1) (i : Fin n) :
    deriv (deriv (fun t => Real.log (shareSum (Function.update s i t) x i))) (s i) ≤
      1 / 4 - Real.exp (s i) / (1 + Real.exp (s i)) ^ 2 := by sorry

end Fundraising.Competition
