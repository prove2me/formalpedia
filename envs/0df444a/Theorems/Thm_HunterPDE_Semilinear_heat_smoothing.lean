-- Prove2me | Theorems.Thm_HunterPDE_Semilinear_heat_smoothing
-- name    : HunterPDE.Semilinear.heat_smoothing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:13:19.974988+00:00
-- url     : https://prove2.me/theorems/fef01ac5-70c3-41ae-aac7-b2effca558d6
-- title:
--   Lemma 5.50 — smoothing of the heat semigroup: ‖e^{−tA}‖_{L(L², H^{2α})} ≤ Ce^t/t^α
-- statement:
--   Let $e^{-tA}$ be the heat semigroup on $\mathbb{R}^n$ and $\alpha > 0$. If $t > 0$, then $e^{-tA}$ maps $L^2(\mathbb{R}^n)$ into $H^{2\alpha}(\mathbb{R}^n)$, and there is a constant $C = C(\alpha, n)$, independent of $t$ and $h$, such that
--   $$\|e^{-tA}h\|_{H^{2\alpha}} \le \frac{C e^t}{t^\alpha}\, \|h\|_{L^2} \qquad \text{for every } h \in L^2(\mathbb{R}^n),\ t > 0,$$
--   i.e. $\|e^{-tA}\|_{\mathcal L(L^2, H^{2\alpha})} \le C e^t / t^\alpha$.
--
--   This quantifies the instantaneous smoothing of the heat equation; for $\alpha < 1$ the bound is integrable as $t \to 0^+$, which is what makes the Duhamel map a contraction.
--
--   **Formalization Note.** $h$ is complex-valued; the operator-norm bound is stated as the equivalent bound for every $h \in L^2$. The $H^{2\alpha}$ norm uses the book's Fourier normalization (Definition 5.74) and is valued in $[0,\infty]$; finiteness is stated as a separate clause.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 154, Lemma 5.50

import Mathlib
import Definitions.Def_HunterPDE_Semilinear_SobolevHs
import Definitions.Def_HunterPDE_Semilinear_HeatSemigroup

open MeasureTheory
open scoped ENNReal

namespace HunterPDE.Semilinear

/-- Lemma 5.50 of Hunter, *Notes on PDEs* (p. 154): let `e^{−tA}` be the heat semigroup (5.37)
and `α > 0`. If `t > 0`, then `e^{−tA} : L²(ℝⁿ) → H^{2α}(ℝⁿ)`, and there is a constant
`C = C(α, n)` such that `‖e^{−tA}‖_{L(L², H^{2α})} ≤ C e^t / t^α`.

The operator-norm bound is stated as the equivalent bound
`‖e^{−tA}h‖_{H^{2α}} ≤ (C e^t / t^α) ‖h‖_{L²}` for every `h ∈ L²(ℝⁿ)` (complex-valued); `C` is
chosen before `t` and `h`. -/
theorem heat_smoothing (n : ℕ) (α : ℝ) (hα : 0 < α) :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t → ∀ h : EuclideanSpace ℝ (Fin n) → ℂ, MemLp h 2 volume →
      hsNorm n (2 * α) (heatSemigroup n t h) < ⊤ ∧
      hsNorm n (2 * α) (heatSemigroup n t h) ≤
        ENNReal.ofReal (C * Real.exp t / t ^ α) * eLpNorm h 2 volume := by sorry

end HunterPDE.Semilinear
