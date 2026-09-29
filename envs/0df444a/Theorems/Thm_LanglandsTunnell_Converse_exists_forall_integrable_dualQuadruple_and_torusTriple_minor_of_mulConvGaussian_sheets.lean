-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_exists_forall_integrable_dualQuadruple_and_torusTriple_minor_of_mulConvGaussian_sheets
-- name    : LanglandsTunnell.Converse.exists_forall_integrable_dualQuadruple_and_torusTriple_minor_of_mulConvGaussian_sheets
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/992960c3-2f80-564a-8d79-49cf054614ba
-- title:
--   Integrability of dual four- and three-variable minor integrands
-- statement:
--   Fix $\nu_1,\nu_2\in\mathbb C$ and $a_1,a_2\in\mathbb Z/2$, and let $W:\mathbb R\to\mathbb C$ be continuous on $\{t\neq0\}$ whose two parity sheets are explicit Gaussian Mellin convolutions: for every $b\in\mathbb Z/2$ and every $t>0$, $W(t)+(-1)^{b}W(-t)=t\cdot 4\int_0^\infty r^{\nu_1+\delta(a_1+b)}e^{-\pi r^2}\,(t/r)^{\nu_2+\delta(a_2+b)}e^{-\pi (t/r)^2}\,dr/r$, where $\delta(c)=0$ for $c=0$ and $1$ otherwise. Let $P_2$ be a real archimedean parameter, $D$ an archimedean Whittaker datum for $P_2$ (a function $D.W$ on real $2\times2$ matrices, smooth on the invertible locus, with the unipotent and central transformation laws, entire zeta functions satisfying the functional equation, and the prescribed decay), let $a\neq0$ be real, $u_0,c_P\in\mathbb C$ and $a_0,s_P\in\mathbb Z/2$. Then there is $\sigma\in\mathbb R$ such that for every $s$ with $\operatorname{Re}s>\sigma$ both of the following hold. First, the function of $(x,t,q,p)$ given by $x^{2s-c_P-P_2.\mathrm{centralExponent}+1}e^{-\pi x^2q^2}$ times the product of sign characters $\mathrm{quasiChar}\,0\,s_P(-t)\cdot\mathrm{quasiChar}\,0\,a_0(-t)\cdot\mathrm{quasiChar}\,0\,1\,t\cdot\mathrm{quasiChar}\,0\,1\,q\cdot\mathrm{quasiChar}\,0\,a_0\,q$ (each $\mathrm{quasiChar}\,0\,c\,y$ being $1$ if $c=0$ and $\operatorname{sign}y$ otherwise), times $W(-t)\,(a+tp^2)\,D.W(\mathrm{diag}(a|t|p/q,1))$, times $|t|^{s-5/2-c_P-P_2.\mathrm{centralExponent}}|q|^{u_0+1}p^{u_0-P_2.\mathrm{centralExponent}-3}$, times $e^{-\pi t^2p^2}e^{-\pi a^2/p^2}e^{-\pi a^2/q^2}$, is integrable on $(0,\infty)\times\mathbb R\times\mathbb R\times(0,\infty)$ for the product of Lebesgue measure restricted to $(0,\infty)$ in the first and fourth variables with Lebesgue measure in the second and third. Secondly, for all $b_0,b_1\in\mathbb C$ the analogous function of $(t,q,p)$, with $(a+tp^2)$ replaced by $b_0a+b_1tp^2$ and the exponent of $|q|$ replaced by $u_0+c_P+P_2.\mathrm{centralExponent}-2s-1$, is integrable on $\mathbb R\times\mathbb R\times(0,\infty)$.
--
--   This supplies the absolute-convergence hypotheses licensing the Fubini interchanges and the splitting of the bracket $b_0a+b_1tp^2$ in the dual (Kirillov-type) evaluation of the archimedean minor section for weight-one Gaussian profiles. It is used in the computation of the dual torus pair as an archimedean root number times an explicit factor and a gamma factor, in [`LanglandsTunnell.RankinSelberg.exists_dualTorusPair_eq_archRootNumber_mul_explicit_mul_gammaFactor_of_weightOne_of_minorSection_gaussian3_of_profile`](thm.html#LanglandsTunnell.RankinSelberg.exists_dualTorusPair_eq_archRootNumber_mul_explicit_mul_gammaFactor_of_weightOne_of_minorSection_gaussian3_of_profile).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_exists_forall_integrable_dualQuadruple_and_torusTriple_minor_of_mulConvGaussian_sheets.lean

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

theorem LanglandsTunnell.Converse.exists_forall_integrable_dualQuadruple_and_torusTriple_minor_of_mulConvGaussian_sheets
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
          (W (-r.2.1) * ((a : ℂ) + (r.2.1 : ℂ) * (r.2.2.2 : ℂ) ^ 2) * D.W (ArchR.diagOne (a * |r.2.1| * r.2.2.2 / r.2.2.1))) *
          ((((|r.2.1| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|r.2.2.1| : ℝ) : ℂ) ^ (u₀ + 1)) *
            (((r.2.2.2 : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * r.2.1 ^ 2 * r.2.2.2 ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / r.2.2.2 ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / r.2.2.1 ^ 2)) : ℂ)))) (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0))))) ∧
      ∀ b₀ b₁ : ℂ, Integrable (fun q : ℝ × ℝ × ℝ =>
        (ArchR.quasiChar 0 sP (-q.1) * ArchR.quasiChar 0 a₀ (-q.1) * ArchR.quasiChar 0 1 q.1 * ArchR.quasiChar 0 1 q.2.1 * ArchR.quasiChar 0 a₀ q.2.1) *
          (W (-q.1) * (b₀ * (a : ℂ) + b₁ * ((q.1 : ℂ) * (q.2.2 : ℂ) ^ 2)) * D.W (ArchR.diagOne (a * |q.1| * q.2.2 / q.2.1))) *
          ((((|q.1| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|q.2.1| : ℝ) : ℂ) ^ (u₀ + cP + P₂.centralExponent - 2 * s - 1)) *
            (((q.2.2 : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * q.1 ^ 2 * q.2.2 ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q.2.2 ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q.2.1 ^ 2)) : ℂ))) ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))) := by sorry
