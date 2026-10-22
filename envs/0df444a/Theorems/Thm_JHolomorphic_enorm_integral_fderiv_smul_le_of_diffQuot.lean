-- Prove2me | Theorems.Thm_JHolomorphic_enorm_integral_fderiv_smul_le_of_diffQuot
-- name    : JHolomorphic.enorm_integral_fderiv_smul_le_of_diffQuot
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T20:47:13.544467+00:00
-- url     : https://prove2.me/theorems/07960701-0c1f-4fd9-a4dc-5124d65cf94b
-- title:
--   Bounded $L^p$ difference quotients bound the pairing $\int (D\varphi\, v) f$ by $\|\varphi\|_{L^q}$
-- statement:
--   Let $1<p<\infty$ and $q=p/(p-1)$, let $E$ be a real normed space, let $c\in\mathbb{C}$, $r<R$, and let $f:\mathbb{C}\to E$ be integrable on $B(c,R)$. Let $v\in\mathbb{C}$ with $|v|=1$, and suppose there are $\delta>0$ and $C$ such that for every real $h$ with $0<|h|<\delta$
--   $$\Bigl\|\frac{f(\cdot+hv)-f}{h}\Bigr\|_{L^p(B(c,r))}\le C.$$
--   Then for every real $C^\infty$ function $\varphi$ with compact support in $B(c,r)$,
--   $$\Bigl\|\int_{\mathbb{C}}\bigl(D\varphi(z)\,v\bigr)\,f(z)\,dz\Bigr\|\le C\,\|\varphi\|_{L^q(B(c,r))}.$$
--   This bounds the distributional derivative of $f$ in the direction $v$ as a functional on $L^q(B(c,r))$.
--
--   **Formalization Note** The difference quotient is `fun z => h⁻¹ • (f (z + (h : ℂ) * v) - f z)`. Norms are `eLpNorm` with exponents `ENNReal.ofReal p` and `ENNReal.ofReal (p / (p - 1))` for the Lebesgue measure restricted to `ball c r`; the bound is `ENNReal.ofReal C`, and the conclusion is stated with the extended norm `‖·‖ₑ`, so no sign condition on $C$ is needed. Test functions satisfy `ContDiff ℝ ∞ φ`, `HasCompactSupport φ` and `tsupport φ ⊆ ball c r`; the integral is over all of $\mathbb{C}$.
-- source:
--   Standard; cf. L. C. Evans, Partial Differential Equations, §5.8.2, proof of Theorem 3 (ii)

import Definitions.Def_JHolomorphic_Setting
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.MeanValue

namespace JHolomorphic

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal

/-- Let `1 < p < ∞`, `r < R`, `f` integrable on `B(c, R)`, and `v` a unit vector. If the difference
quotients `h⁻¹ (f(· + h v) - f)` have `L^p(B(c, r))` norm at most `C` for all real `h` with
`0 < |h| < δ`, then for every real `C^∞` function `φ` with compact support in `B(c, r)`,
`‖∫ (Dφ · v) f‖ ≤ C ‖φ‖_{L^q(B(c, r))}`, where `q = p / (p - 1)`. -/
theorem enorm_integral_fderiv_smul_le_of_diffQuot {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (p : ℝ) (hp : 1 < p) {c : ℂ} {r R : ℝ} (hrR : r < R) {f : ℂ → E}
    (hf : IntegrableOn f (ball c R)) (v : ℂ) (hv : ‖v‖ = 1) (δ : ℝ) (hδ : 0 < δ) (C : ℝ)
    (hC : ∀ h : ℝ, h ≠ 0 → |h| < δ →
      eLpNorm (fun z => h⁻¹ • (f (z + (h : ℂ) * v) - f z)) (ENNReal.ofReal p)
        (volume.restrict (ball c r)) ≤ ENNReal.ofReal C)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ ball c r) :
    ‖∫ z, fderiv ℝ φ z v • f z‖ₑ ≤
      ENNReal.ofReal C * eLpNorm φ (ENNReal.ofReal (p / (p - 1))) (volume.restrict (ball c r)) := by
  sorry

end JHolomorphic
