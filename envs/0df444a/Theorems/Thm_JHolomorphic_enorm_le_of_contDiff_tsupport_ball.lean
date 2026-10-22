-- Prove2me | Theorems.Thm_JHolomorphic_enorm_le_of_contDiff_tsupport_ball
-- name    : JHolomorphic.enorm_le_of_contDiff_tsupport_ball
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T21:06:07.279452+00:00
-- url     : https://prove2.me/theorems/41756e2d-b0c5-415a-8f6b-f1cc9d5d2dd3
-- title:
--   Sup bound for compactly supported $C^1$ maps on a disc in terms of $L^p$ norms of the partials, $p>2$
-- statement:
--   Let $E$ be a real Banach space and $p>2$. There is a constant $C$, depending only on $p$, such that for every disc $B(c,r)\subseteq\mathbb{C}$ ($r>0$) and every $C^1$ map $g:\mathbb{C}\to E$ whose closed support lies in $B(c,r)$,
--   $$\|g(z)\|\;\le\;C\,r^{1-2/p}\big(\|\partial_s g\|_{L^p(\mathbb{C})}+\|\partial_t g\|_{L^p(\mathbb{C})}\big)\qquad\text{for all } z\in\mathbb{C},$$
--   where $z=s+it$, $\partial_s g=Dg(\cdot)\,1$ and $\partial_t g=Dg(\cdot)\,i$. This is Morrey's sup bound in the plane, with the scaling in the radius made explicit. It is the smooth case of the corresponding bound for continuous $W^{1,p}$ maps with compact support in a disc.
--
--   **Formalization Note** The norm on the left is `‖g z‖ₑ`. The constant enters as `ENNReal.ofReal (C * r ^ (1 - 2 / p))`, and the $L^p$ norms are `eLpNorm (fun y => fderiv ℝ g y 1) (ENNReal.ofReal p) volume` and the same with `Complex.I`, for Lebesgue measure on $\mathbb{C}$. $C$ is chosen before $c$, $r$ and $g$. The hypotheses are `ContDiff ℝ 1 g` and `tsupport g ⊆ ball c r`.
-- source:
--   Standard (Morrey's inequality in dimension 2); cf. L. C. Evans, Partial Differential Equations, §5.6.2, Theorem 4.

import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs

namespace JHolomorphic

open MeasureTheory Metric

/-- Let `p > 2`. There is a constant `C` such that for every disc `B(c, r) ⊆ ℂ` and every `C¹` map
`g : ℂ → E` into a complete real normed space with `tsupport g ⊆ B(c, r)`, one has
`‖g(z)‖ ≤ C r^{1-2/p} (‖∂ₛg‖_{L^p} + ‖∂ₜg‖_{L^p})` for every `z ∈ ℂ`. -/
theorem enorm_le_of_contDiff_tsupport_ball {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (p : ℝ) (hp : 2 < p) :
    ∃ C : ℝ, ∀ (c : ℂ) (r : ℝ), 0 < r → ∀ g : ℂ → E, ContDiff ℝ 1 g →
      tsupport g ⊆ ball c r → ∀ z, ‖g z‖ₑ ≤ ENNReal.ofReal (C * r ^ (1 - 2 / p)) *
        (eLpNorm (fun y => fderiv ℝ g y 1) (ENNReal.ofReal p) volume +
          eLpNorm (fun y => fderiv ℝ g y Complex.I) (ENNReal.ofReal p) volume) := by
  sorry

end JHolomorphic
