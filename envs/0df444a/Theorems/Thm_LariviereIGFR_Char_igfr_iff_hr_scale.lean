-- Prove2me | Theorems.Thm_LariviereIGFR_Char_igfr_iff_hr_scale
-- name    : LariviereIGFR.Char.igfr_iff_hr_scale
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:39:10.48554+00:00
-- url     : https://prove2.me/theorems/b4035511-ec86-4136-baf7-8fda54b208b9
-- title:
--   Proof of Theorem 1, p. 603 — parts 1 ⇔ 3: X is IGFR iff X ⪯hr λX for every λ ≥ 1
-- statement:
--   Let $X \ge 0$ have law $\mu$ with regular density $\varphi$. For $\lambda \ge 1$ give $\lambda X$ its density $\varphi_\lambda(\xi) = \varphi(\xi/\lambda)/\lambda$. Then
--   $$X \text{ is IGFR} \iff X \preceq_{hr} \lambda X \ \text{ for every } \lambda \ge 1,$$
--   where $X \preceq_{hr} \lambda X$ means $h(\xi) \ge h_\lambda(\xi)$ for every $\xi \ge 0$ with $\Phi(\xi) < 1$, $h$ and $h_\lambda$ being the failure rates of $X$ and $\lambda X$.
--
--   This is the equivalence of parts 1 and 3 of Theorem 1: an IGFR variable becomes smaller in the hazard rate order when it is scaled up.
--
--   **Formalization Note** The order is restricted to $\Phi(\xi) < 1$ because there the paper's $h(\xi)$ is finite; where $\bar\Phi(\xi) = 0$ the paper's $h$ is $+\infty$ and the inequality holds trivially. Only $\lambda \ge 1$ is quantified, as printed.
-- source:
--   Lariviere, A note on probability distributions with increasing generalized failure rates, Oper. Res. 54(3) (2006), p. 603, §2, proof of Theorem 1 ("To link parts 1 and 3, note that the generalized failure rate of λX is g_λ(ξ) = g(ξ/λ).")

import Mathlib
import Definitions.Def_LariviereIGFR_Char_Setting

namespace LariviereIGFR.Char

open MeasureTheory ProbabilityTheory

theorem igfr_iff_hr_scale (μ : Measure ℝ) [IsProbabilityMeasure μ] (φ : ℝ → ℝ)
    (hnn : μ (Set.Iio 0) = 0) (hφ : IsRegDensity μ φ) :
    IsIGFR μ φ ↔
      ∀ c : ℝ, 1 ≤ c →
        HazardRateLE μ φ (μ.map (fun x => c * x)) (fun ξ => φ (ξ / c) / c) := by sorry

end LariviereIGFR.Char
