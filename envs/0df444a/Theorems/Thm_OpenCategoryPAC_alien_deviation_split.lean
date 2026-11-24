-- Prove2me | Theorems.Thm_OpenCategoryPAC_alien_deviation_split
-- name    : OpenCategoryPAC.alien_deviation_split
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T04:21:10.014904+00:00
-- url     : https://prove2.me/theorems/39b7d0f5-4bdf-4282-82d2-06ab0e2385bf
-- title:
--   Theorem 1, proof: the deviation of $\hat F_a$ is split between $\hat F_m$ and $\hat F_0$
-- statement:
--   Let $\mu_0,\mu_a$ be probability measures on $\mathbb R$, $0<\alpha\le1$, $\mu_m=(1-\alpha)\mu_0+\alpha\mu_a$, and let $F_0,F_a,F_m$ be their CDFs. Let $\epsilon>0$, let $x_1,\dots,x_n$ and $y_1,\dots,y_n$ be any real numbers, and let $\hat F_0,\hat F_m$ be their empirical CDFs and $\hat F_a=(\hat F_m-(1-\alpha)\hat F_0)/\alpha$. If
--
--   $$\sup_t|\hat F_a(t)-F_a(t)|>\epsilon,$$
--
--   then
--
--   $$\sup_t|\hat F_m(t)-F_m(t)|>\frac{\alpha}{2-\alpha}\epsilon\quad\text{or}\quad\sup_t|\hat F_0(t)-F_0(t)|>\frac{\alpha}{2-\alpha}\epsilon.$$
--
--   This is the deterministic content of the first chain of inequalities in the proof of Theorem 1: the event that $\hat F_a$ deviates by more than $\epsilon$ is contained in the union of the two events on the right.
-- source:
--   Liu, Garrepalli, Dietterich, Fern and Hendrycks, Open Category Detection with PAC Guarantees, arXiv:1808.00529v1 (ICML 2018), Appendix A (Proof for Theorem 1), first chain of inequalities, p. 8

import Mathlib
import Definitions.Def_OpenCategoryPAC_Basic

open MeasureTheory ProbabilityTheory Filter Topology

namespace OpenCategoryPAC

theorem alien_deviation_split (μ0 μa μm : Measure ℝ) [IsProbabilityMeasure μ0]
    [IsProbabilityMeasure μa] [IsProbabilityMeasure μm] (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hm : μm = mixture α μ0 μa) (ε : ℝ) (hε : 0 < ε) {n : ℕ} (x y : Fin n → ℝ)
    (h : ε < supDev (alienCDFEst α x y) (cdf μa)) :
    α / (2 - α) * ε < supDev (empCDF y) (cdf μm) ∨
      α / (2 - α) * ε < supDev (empCDF x) (cdf μ0) := by sorry

end OpenCategoryPAC
