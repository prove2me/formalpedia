-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_exists_forall_integrable_dualQuadruple_and_torusTriple_conjBlock_of_mulConvGaussian_sheets
-- name    : LanglandsTunnell.Converse.exists_forall_integrable_dualQuadruple_and_torusTriple_conjBlock_of_mulConvGaussian_sheets
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/1b6e3215-a0b7-538b-85c3-11cd6babf4f4
-- title:
--   Integrability of the flat dual quadruple and torus-triple integrands
-- statement:
--   Let $\nu_1,\nu_2\in\mathbb{C}$, $a_1,a_2\in\mathbb{Z}/2$ and let $W:\mathbb{R}\to\mathbb{C}$ be continuous on $\{t\neq 0\}$ and satisfy, for each $b\in\mathbb{Z}/2$ and each $t>0$, the two-sheet Gaussian multiplicative-convolution identity $W(t)+(-1)^{b}W(-t)=t\cdot 4\int_0^\infty r^{\nu_1+\varepsilon(a_1+b)}e^{-\pi r^2}\,(t/r)^{\nu_2+\varepsilon(a_2+b)}e^{-\pi(t/r)^2}\,dr/r$, where $\varepsilon(a)=0$ for $a=0$ and $1$ otherwise. Let $P_2$ be a real archimedean parameter with central exponent $c_2$, let $D$ be a real archimedean Whittaker datum for $P_2$ (a Whittaker function $D.W$ on $2\times2$ real matrices with the unipotent and central laws, entire zeta functions with functional equation and finite order, and the prescribed decay), let $a\neq0$ be real, $u_0,c_P\in\mathbb{C}$, $a_0,s_P\in\mathbb{Z}/2$ and $n\in\mathbb{N}$. Then there is $\sigma\in\mathbb{R}$ such that for every $s$ with $\operatorname{Re}s>\sigma$ both of the following hold. First, the function $$x^{2s-c_P-c_2+n}e^{-\pi x^2q^2}\cdot \chi\cdot W(-t)\bigl(-(a+tp^2+ap\,\mathrm{sgn}(t)q^{-1})\bigr)D.W\!\left(\begin{smallmatrix}a|t|p/q&0\\0&1\end{smallmatrix}\right)\cdot|t|^{s-5/2-c_P-c_2}|q|^{u_0+n}p^{u_0-c_2-3}\cdot e^{-\pi t^2p^2}e^{-\pi a^2/p^2}e^{-\pi a^2/q^2},$$ where $\chi$ is the product of sign characters $\mathrm{sgn}(-t)^{s_P}\mathrm{sgn}(-t)^{a_0}\mathrm{sgn}(t)\,\mathrm{sgn}(q)^{n}\mathrm{sgn}(q)^{a_0}$ (each factor being $1$ when its index vanishes in $\mathbb{Z}/2$), is integrable in $(x,t,q,p)$ for Lebesgue measure on $(0,\infty)\times\mathbb{R}\times\mathbb{R}\times(0,\infty)$. Secondly, for all $b_0,b_1,b_2\in\mathbb{C}$ the three-variable function obtained by replacing the bracket by $b_0a+b_1tp^2+b_2\,ap\,\mathrm{sgn}(t)q^{-1}$, omitting the $x$-factors and replacing the exponent of $|q|$ by $u_0+c_P+c_2-2s-1$, is integrable in $(t,q,p)$ on $\mathbb{R}\times\mathbb{R}\times(0,\infty)$.
--
--   This supplies the absolute-convergence and Fubini licences for the archimedean dual computation in the converse direction of the Jacquet–Langlands correspondence used in the Langlands–Tunnell argument: the four-variable claim governs the dual unfolding of the flat (conjugate-block, weight $n+1$) section, and the weighted three-variable claim covers the individual monomial terms appearing after folding. It is cited by the identities evaluating these integrals as a Gamma-factor times an explicit product, for discrete and two-sheet profiles, and by the corresponding Rankin–Selberg dual torus-pair evaluation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_exists_forall_integrable_dualQuadruple_and_torusTriple_conjBlock_of_mulConvGaussian_sheets.lean

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

theorem LanglandsTunnell.Converse.exists_forall_integrable_dualQuadruple_and_torusTriple_conjBlock_of_mulConvGaussian_sheets
    (ν₁ ν₂ : ℂ) (a₁ a₂ : ZMod 2)
    (W : ℝ → ℂ) (hWc : ContinuousOn W {t : ℝ | t ≠ 0})
    (hW : ∀ b : ZMod 2, ∀ t : ℝ, 0 < t →
      W t + (-1 : ℂ) ^ b.val * W (-t) =
        (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (a₁ + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂ + signShift (a₂ + b)) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (a : ℝ) (ha : a ≠ 0) (u₀ cP : ℂ) (a₀ sP : ZMod 2) (n : ℕ) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Integrable (fun r : ℝ × ℝ × ℝ × ℝ =>
        (((r.1 : ℝ) : ℂ) ^ (2 * s - cP - P₂.centralExponent + n) * (Real.exp (-(Real.pi * r.1 ^ 2 * r.2.2.1 ^ 2)) : ℂ)) *
        ((ArchR.quasiChar 0 sP (-r.2.1) * ArchR.quasiChar 0 a₀ (-r.2.1) * ArchR.quasiChar 0 1 r.2.1 * ArchR.quasiChar 0 (n : ZMod 2) r.2.2.1 * ArchR.quasiChar 0 a₀ r.2.2.1) *
          (W (-r.2.1) * (-((a : ℂ) + (r.2.1 : ℂ) * (r.2.2.2 : ℂ) ^ 2 + (a : ℂ) * (r.2.2.2 : ℂ) * ArchR.quasiChar 0 1 r.2.1 * ((r.2.2.1⁻¹ : ℝ) : ℂ))) * D.W (ArchR.diagOne (a * |r.2.1| * r.2.2.2 / r.2.2.1))) *
          ((((|r.2.1| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|r.2.2.1| : ℝ) : ℂ) ^ (u₀ + n)) *
            (((r.2.2.2 : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * r.2.1 ^ 2 * r.2.2.2 ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / r.2.2.2 ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / r.2.2.1 ^ 2)) : ℂ)))) (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0))))) ∧
      ∀ b₀ b₁ b₂ : ℂ, Integrable (fun q : ℝ × ℝ × ℝ =>
        (ArchR.quasiChar 0 sP (-q.1) * ArchR.quasiChar 0 a₀ (-q.1) * ArchR.quasiChar 0 1 q.1 * ArchR.quasiChar 0 (n : ZMod 2) q.2.1 * ArchR.quasiChar 0 a₀ q.2.1) *
          (W (-q.1) * (b₀ * (a : ℂ) + b₁ * ((q.1 : ℂ) * (q.2.2 : ℂ) ^ 2) + b₂ * ((a : ℂ) * (q.2.2 : ℂ) * ArchR.quasiChar 0 1 q.1 * ((q.2.1⁻¹ : ℝ) : ℂ))) * D.W (ArchR.diagOne (a * |q.1| * q.2.2 / q.2.1))) *
          ((((|q.1| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|q.2.1| : ℝ) : ℂ) ^ (u₀ + cP + P₂.centralExponent - 2 * s - 1)) *
            (((q.2.2 : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * q.1 ^ 2 * q.2.2 ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q.2.2 ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q.2.1 ^ 2)) : ℂ))) ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))) := by sorry
