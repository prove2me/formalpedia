-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_proposition_4_ii
-- name    : ManyServerQED.Scheduling.proposition_4_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:04:21.048148+00:00
-- url     : https://prove2.me/theorems/8753ef67-4663-413b-8454-70d13aa523dc
-- title:
--   Proposition 4(ii) — polynomial moment bounds for the controlled diffusion
-- statement:
--   Let $(\ell,\mu,\theta,r)$ be diffusion data. For every $m\in\{1,2,\dots\}$ there is a constant $c_m$, depending only on these data and $m$, such that for every admissible system $\pi$, initial point $x$ and controlled process $X$,
--   $$
--   E^\pi_x\|X(t)\|^m\le c_m\,(1+\|x\|^m)(1+t^m),\qquad t\ge0.
--   $$
--
--   These moment bounds make the discounted costs finite and drive Proposition 5(i).
--
--   **Formalization Note** $\|\cdot\|$ is the $\ell^1$ norm, also for the paper's $|X(t)|$. The expectation is a lower Lebesgue integral in $[0,\infty]$, so the bound also asserts finiteness. For each $m$ the constant is chosen before $\pi$, $x$ and $t$.
-- source:
--   Atar, Mandelbaum & Reiman, Scheduling a Multi Class Queue with Many Exponential Servers: Asymptotic Optimality in Heavy Traffic, arXiv:math/0407058v1 (reprint of Ann. Appl. Probab. 14(3), 2004), p. 23, Proposition 4(ii)

import Mathlib
import Definitions.Def_ManyServerQED_Scheduling_Diffusion

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ManyServerQED.Scheduling

/-- Proposition 4(ii) (p. 23): for every `m ∈ ℕ = {1, 2, …}` there is a constant `c_m`, depending
only on the diffusion data and `m`, such that `E^π_x ‖X(t)‖^m ≤ c_m (1 + ‖x‖^m)(1 + t^m)` for every
admissible system `π`, initial point `x`, controlled process `X` and `t ≥ 0`. -/
theorem proposition_4_ii {k : ℕ} [NeZero k] (D : DiffusionData k) :
    ∀ m : ℕ, 1 ≤ m → ∃ c : ℝ, ∀ (π : AdmissibleSystem k) (x : Fin k → ℝ)
      (X : ℝ≥0 → π.Ω → Fin k → ℝ), IsControlledProcess D π x X → ∀ t : ℝ≥0,
        ∫⁻ ω, ENNReal.ofReal (l1norm (X t ω)) ^ m ∂π.P ≤
          ENNReal.ofReal (c * (1 + l1norm x ^ m) * (1 + (t : ℝ) ^ m)) := by sorry

end ManyServerQED.Scheduling
