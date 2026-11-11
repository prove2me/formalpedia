-- Prove2me | Theorems.Thm_MatrixSenseRank_Testing_fact_19
-- name    : MatrixSenseRank.Testing.fact_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T13:47:02.554178+00:00
-- url     : https://prove2.me/theorems/077b6369-e4a9-4f2b-8ce3-3ec3e9f8f36f
-- title:
--   Fact 19 — product-normal transform on the complex strip
-- statement:
--   Let $G,H$ be independent $N(0,1)$ random variables and write $Z=GH$. For every complex $s$ with $|\operatorname{Re}s|<1$, the complex exponential is Bochner integrable and
--   $$\mathbb E e^{sZ}=\frac1{\sqrt{1-s^2}},$$
--   where the square root is the principal complex branch. In particular,
--   $$\mathbb E e^{itZ}=(1+t^2)^{-1/2}\quad(t\in\mathbb R),\qquad
--   \mathbb E e^{\lambda Z}=(1-\lambda^2)^{-1/2}\quad(|\lambda|<1).$$
--   Integrability is asserted for both specializations as well. This identifies the transform of the scalar law used by the matrix tester; it places no MGF condition on the additive noise.
--
--   Differences from the source:
--   - encoding: independent standard normal random variables G and H → the multiplication pushforward of their product probability law and explicit Bochner integrability of each displayed exponential; reason: expectations depend only on the law; integrability makes the complex and real expectations finite in exactly the stated domains
-- source:
--   Yiqiao Bao, Anindya De, Shivam Nadimpalli, Rocco A. Servedio, Chenyang Sun, Nathan White, STOC 2027 submission #380 (October 2026), §7.1.2, Fact 19, printed pp. 31–32 / PDF pp. 32–33; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/380.pdf; PDF SHA-256 6e4e46ced4dfe65bbe94e4cec3e8230032914efef9d87b0f544bbea151a00c3b.

import Mathlib
import Definitions.Def_MatrixSenseRank_Testing_Moments

set_option autoImplicit false
open MeasureTheory

namespace MatrixSenseRank.Testing

/-- Fact 19, printed pp. 31–32 / PDF pp. 32–33, full complex strip and both specializations. -/
theorem fact_19 :
    (∀ s : ℂ, |s.re| < 1 →
      Integrable (fun z : ℝ => Complex.exp (s * (z : ℂ))) productNormal ∧
      (∫ z : ℝ, Complex.exp (s * (z : ℂ)) ∂productNormal) =
        (Complex.sqrt (1 - s ^ 2))⁻¹) ∧
    (∀ t : ℝ,
      Integrable (fun z : ℝ => Complex.exp (Complex.I * (t : ℂ) * (z : ℂ))) productNormal ∧
      (∫ z : ℝ, Complex.exp (Complex.I * (t : ℂ) * (z : ℂ)) ∂productNormal) =
        ((Real.sqrt (1 + t ^ 2))⁻¹ : ℝ)) ∧
    (∀ t : ℝ, |t| < 1 →
      Integrable (fun z : ℝ => Real.exp (t * z)) productNormal ∧
      mgfValue productNormal t = (Real.sqrt (1 - t ^ 2))⁻¹) := by sorry

end MatrixSenseRank.Testing
