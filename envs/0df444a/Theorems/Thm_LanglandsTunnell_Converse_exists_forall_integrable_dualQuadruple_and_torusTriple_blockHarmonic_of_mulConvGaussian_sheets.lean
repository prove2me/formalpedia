-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_exists_forall_integrable_dualQuadruple_and_torusTriple_blockHarmonic_of_mulConvGaussian_sheets
-- name    : LanglandsTunnell.Converse.exists_forall_integrable_dualQuadruple_and_torusTriple_blockHarmonic_of_mulConvGaussian_sheets
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/2591b188-42b5-5781-a7e7-f049919f3c4f
-- title:
--   Integrability of dual quadruple and torus-triple integrands
-- statement:
--   Fix $\nu_1,\nu_2\in\mathbb C$, $a_1,a_2\in\mathbb Z/2$ and a function $W:\mathbb R\to\mathbb C$ continuous on $\{t\neq0\}$ whose two parity sheets are prescribed Gaussian Mellin convolutions: for every $b\in\mathbb Z/2$ and every $t>0$, $W(t)+(-1)^{b}W(-t)=4t\int_0^\infty r^{\nu_1+\mathrm{signShift}(a_1+b)}e^{-\pi r^2}(t/r)^{\nu_2+\mathrm{signShift}(a_2+b)}e^{-\pi(t/r)^2}\,\frac{dr}{r}$, where $\mathrm{signShift}(c)=0$ for $c=0$ and $1$ otherwise. Fix further a real archimedean parameter $P_2$ and a datum $D$ for it (a function on $2\times2$ real matrices with the unipotent and central transformation laws attached to $P_2$, smoothness on the invertible locus, entire zeta integrals with functional equation and finite order, and the decay bounds at $0$ and $\infty$), a real $a\neq0$, complex $u_0,c_P$ and $a_0,s_P\in\mathbb Z/2$. Write $c_2=P_2$'s central exponent and $\Sigma(t,q)=\mathrm{sgn}(-t)^{s_P}\mathrm{sgn}(-t)^{a_0}\mathrm{sgn}(t)\,\mathrm{sgn}(q)\,\mathrm{sgn}(q)^{a_0}$ for the product of the five $\mathrm{quasiChar}\,0$ sign characters occurring, and $f_D(y)=D.W(\,!![y,0;0,1]\,)$. Then there is $\sigma\in\mathbb R$ such that for every $s$ with $\operatorname{Re}s>\sigma$ both of the following hold. First, the four-variable function $$(r,t,q,p)\mapsto r^{2s-c_P-c_2+1}e^{-\pi r^2q^2}\,\Sigma(t,q)\,W(-t)\bigl(a+tp^2-a p\,\mathrm{sgn}(t)q^{-1}\bigr)f_D\!\left(\tfrac{a|t|p}{q}\right)|t|^{s-5/2-c_P-c_2}|q|^{u_0+1}p^{u_0-c_2-3}e^{-\pi t^2p^2-\pi a^2/p^2-\pi a^2/q^2}$$ is integrable for Lebesgue measure on $(0,\infty)\times\mathbb R\times\mathbb R\times(0,\infty)$. Second, for all $b_0,b_1,b_2\in\mathbb C$ the three-variable function $$(t,q,p)\mapsto \Sigma(t,q)\,W(-t)\bigl(b_0a+b_1tp^2+b_2\,a p\,\mathrm{sgn}(t)q^{-1}\bigr)f_D\!\left(\tfrac{a|t|p}{q}\right)|t|^{s-5/2-c_P-c_2}|q|^{u_0+c_P+c_2-2s-1}p^{u_0-c_2-3}e^{-\pi t^2p^2-\pi a^2/p^2-\pi a^2/q^2}$$ is integrable on $\mathbb R\times\mathbb R\times(0,\infty)$.
--
--   This supplies the absolute-convergence licences needed to apply Fubini's theorem and to split the three-term bracket in the archimedean Rankin–Selberg computation on the dual side, for weight-one two-sheet Gaussian-convolution profiles. It is used in the evaluation of the dual torus-triple block-harmonic integral in terms of $\Gamma_{\mathbb R}$-factors and in the resulting explicit formula for the dual torus pair with its archimedean root number.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_exists_forall_integrable_dualQuadruple_and_torusTriple_blockHarmonic_of_mulConvGaussian_sheets.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

theorem LanglandsTunnell.Converse.exists_forall_integrable_dualQuadruple_and_torusTriple_blockHarmonic_of_mulConvGaussian_sheets
    (ν₁ ν₂ : ℂ) (a₁ a₂ : ZMod 2)
    (W : ℝ → ℂ) (hWc : ContinuousOn W {t : ℝ | t ≠ 0})
    (hW : ∀ b : ZMod 2, ∀ t : ℝ, 0 < t →
      W t + (-1 : ℂ) ^ b.val * W (-t) =
        (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (a₁ + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂ + signShift (a₂ + b)) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (a : ℝ) (ha : a ≠ 0) (u₀ cP : ℂ) (a₀ sP : ZMod 2) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Integrable (fun r : ℝ × ℝ × ℝ × ℝ =>
        (((r.1 : ℝ) : ℂ) ^ (2 * s - cP - P₂.centralExponent + 1) * (Real.exp (-(Real.pi * r.1 ^ 2 * r.2.2.1 ^ 2)) : ℂ)) *
        ((ArchR.quasiChar 0 sP (-r.2.1) * ArchR.quasiChar 0 a₀ (-r.2.1) * ArchR.quasiChar 0 1 r.2.1 * ArchR.quasiChar 0 1 r.2.2.1 * ArchR.quasiChar 0 a₀ r.2.2.1) *
          (W (-r.2.1) * ((a : ℂ) + (r.2.1 : ℂ) * (r.2.2.2 : ℂ) ^ 2 - (a : ℂ) * (r.2.2.2 : ℂ) * ArchR.quasiChar 0 1 r.2.1 * ((r.2.2.1⁻¹ : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * |r.2.1| * r.2.2.2 / r.2.2.1))) *
          ((((|r.2.1| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|r.2.2.1| : ℝ) : ℂ) ^ (u₀ + 1)) *
            (((r.2.2.2 : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * r.2.1 ^ 2 * r.2.2.2 ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / r.2.2.2 ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / r.2.2.1 ^ 2)) : ℂ)))) (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0))))) ∧
      ∀ b₀ b₁ b₂ : ℂ, Integrable (fun q : ℝ × ℝ × ℝ =>
        (ArchR.quasiChar 0 sP (-q.1) * ArchR.quasiChar 0 a₀ (-q.1) * ArchR.quasiChar 0 1 q.1 * ArchR.quasiChar 0 1 q.2.1 * ArchR.quasiChar 0 a₀ q.2.1) *
          (W (-q.1) * (b₀ * (a : ℂ) + b₁ * ((q.1 : ℂ) * (q.2.2 : ℂ) ^ 2) + b₂ * ((a : ℂ) * (q.2.2 : ℂ) * ArchR.quasiChar 0 1 q.1 * ((q.2.1⁻¹ : ℝ) : ℂ))) * D.W (ArchR.diagOne (a * |q.1| * q.2.2 / q.2.1))) *
          ((((|q.1| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|q.2.1| : ℝ) : ℂ) ^ (u₀ + cP + P₂.centralExponent - 2 * s - 1)) *
            (((q.2.2 : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * q.1 ^ 2 * q.2.2 ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q.2.2 ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q.2.1 ^ 2)) : ℂ))) ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))) := by sorry
