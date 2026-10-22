-- Prove2me | Theorems.Thm_JHolomorphic_eLpNorm_diffQuot_le
-- name    : JHolomorphic.eLpNorm_diffQuot_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T15:56:18.338611+00:00
-- url     : https://prove2.me/theorems/22b1c8e6-aff9-42e1-972a-73df4367c819
-- title:
--   Difference quotients are bounded in $L^q$ by the directional weak derivative
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $U\subseteq\mathbb{C}$ open, and let $f:\mathbb{C}\to E$ have weak partial derivatives $f_s,f_t$ on $U$, with $f,f_s,f_t$ integrable on every compact subset of $U$. Let $1\le q\le\infty$, let $v\in\mathbb{C}$ with $|v|=1$, let $h\in\mathbb{R}\setminus\{0\}$, and let $c\in\mathbb{C}$, $r\in\mathbb{R}$ with $B(c,r+|h|)\subseteq U$. Then
--   $$\Bigl\|\frac{f(\cdot+hv)-f}{h}\Bigr\|_{L^q(B(c,r))}\le\bigl\|(\operatorname{Re}v)\,f_s+(\operatorname{Im}v)\,f_t\bigr\|_{L^q(B(c,r+|h|))}.$$
--   Here $(\operatorname{Re}v)f_s+(\operatorname{Im}v)f_t$ is the weak derivative of $f$ in the direction $v$.
--
--   **Formalization Note** Weak partial derivatives are `HasWeakPartialsOn`, tested against real $C^\infty$ functions with compact support in $U$; $f_s$ is the derivative in the direction $1$ and $f_t$ in the direction $i$. The difference quotient is `fun z => h⁻¹ • (f (z + (h : ℂ) * v) - f z)`. The norms are `eLpNorm _ q` for the Lebesgue measure restricted to the open discs `ball c r` and `ball c (r + |h|)`.
-- source:
--   L. C. Evans, Partial Differential Equations, §5.8.2, Theorem 3 (i); D. Gilbarg, N. Trudinger, Elliptic PDE of Second Order, Lemma 7.23

import Definitions.Def_JHolomorphic_Setting

namespace JHolomorphic

open MeasureTheory Metric
open scoped ContDiff

/-- Let `f : ℂ → E` have weak partials `fₛ`, `fₜ` on the open set `U`, with `f`, `fₛ`, `fₜ`
integrable on compact subsets of `U`, and let `1 ≤ q ≤ ∞`. For a unit vector `v`, a real `h ≠ 0` and a
disc with `B(c, r + |h|) ⊆ U`, the difference quotient `h⁻¹ (f(· + h v) - f)` has `L^q(B(c, r))` norm
at most the `L^q(B(c, r + |h|))` norm of the directional weak derivative `(Re v) fₛ + (Im v) fₜ`. -/
theorem eLpNorm_diffQuot_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (q : ENNReal) (hq : 1 ≤ q) {U : Set ℂ} (hU : IsOpen U)
    {f fs ft : ℂ → E} (hw : HasWeakPartialsOn U f fs ft)
    (hi : ∀ K ⊆ U, IsCompact K → IntegrableOn f K ∧ IntegrableOn fs K ∧ IntegrableOn ft K)
    (v : ℂ) (hv : ‖v‖ = 1) (c : ℂ) (r h : ℝ) (hh : h ≠ 0) (hb : ball c (r + |h|) ⊆ U) :
    eLpNorm (fun z => h⁻¹ • (f (z + (h : ℂ) * v) - f z)) q (volume.restrict (ball c r)) ≤
      eLpNorm (fun z => v.re • fs z + v.im • ft z) q (volume.restrict (ball c (r + |h|))) := by
  sorry

end JHolomorphic
