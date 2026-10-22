-- Prove2me | Theorems.Thm_GenStieltjes_ExactOrder_theorem_A1_inversion
-- name    : GenStieltjes.ExactOrder.theorem_A1_inversion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:46:10.903232+00:00
-- url     : https://prove2.me/theorems/af23df98-2bfa-4f71-88a1-ad8a6b61f853
-- title:
--   Theorem A1, inversion (29), case $n=[\eta]=0$ — $F_\mu(y)=\frac{1}{\Gamma(1-\eta)}\int_{[0,y)}\frac{\nu(du)}{(y-u)^\eta}$
-- statement:
--   Let $\alpha>0$, $0<\eta<1$, let $\mu\in\mathcal M_\alpha$ be a measure on $[0,\infty)$, and let $\nu=I^+_\eta\mu$ be its Riemann–Liouville fractional integral of order $\eta$ (Definition A1). Then for every $y\ge 0$ the left-continuous distribution function $F_\mu(y)=\mu([0,y))$ is recovered from $\nu$ by
--   $$F_\mu(y)=\frac{1}{\Gamma(1-\eta)}\int_{[0,y)}\frac{\nu(du)}{(y-u)^{\eta}} .$$
--
--   This is formula (29) in the case $n=[\eta]=0$, where no differentiation is needed. It is the inversion step in both directions of the proof of Theorem 16.
--
--   **Formalization Note** Only $n=0$ is stated. For $n\ge1$ the printed formula differentiates the $n$-fold iterated integral of $F_\mu$ exactly $n$ times, which is not defined at the jumps of $F_\mu$; Theorem 16 uses only $n=0$. Both sides are valued in $[0,\infty]$.
-- source:
--   Karp & Prilepkina, Generalized Stieltjes transforms: basic aspects, arXiv:1111.4271v2, p. 16, Theorem A1, formula (29) with n = 0

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P11
import Definitions.Def_GenStieltjes_ExactOrder_Basic

namespace GenStieltjes.ExactOrder

open MeasureTheory
open scoped NNReal ENNReal
open QAlgorithms.Papers.Independent.Renew46.P11 (PositiveReal StieltjesRepresentation StieltjesClass)

/-- Theorem A1, inversion (29), case `n = [η] = 0`, p. 16: if `μ ∈ M_α` and `0 < η < 1`,
then for every `y ≥ 0`,
`F_μ(y) = (1/Γ(1 − η)) ∫_{[0,y)} ν(du) / (y − u)^η` with `ν = I^+_η μ`. -/
theorem theorem_A1_inversion (α η : ℝ) (hα : 0 < α) (hη : 0 < η) (hη1 : η < 1)
    (μ : Measure ℝ≥0) (hμ : InM α μ) (y : ℝ≥0) :
    distFn μ y =
      ENNReal.ofReal (1 / Real.Gamma (1 - η)) *
        ∫⁻ u in Set.Iio y,
          ENNReal.ofReal (((y : ℝ) - (u : ℝ)) ^ (-η)) ∂(rlIntegral η μ) := by sorry

end GenStieltjes.ExactOrder
