-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_dualTorusPair_iwasawa_eq_const_mul_integral_torusTriple_minor_of_re_gt
-- name    : LanglandsTunnell.Converse.dualTorusPair_iwasawa_eq_const_mul_integral_torusTriple_minor_of_re_gt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/09e488e4-806a-5e8c-b233-d58dcba956d9
-- title:
--   Iwasawa-unfolded dual torus pair as a torus-triple integral
-- statement:
--   Fix a real archimedean parameter $P_2$ (either a principal pair $(u_1,a_1,u_2,a_2)$ with central exponent $u_1+u_2$, or a discrete parameter $(u,k)$ with central exponent $2u$), a real archimedean Whittaker datum $D$ for $P_2$ (a function $D.W$ on real $2\times 2$ matrices, smooth on the invertible locus, satisfying $D.W(n(x)g)=e^{2\pi i x}D.W(g)$ and the central law for $P_2$, with entire zeta functions, functional equation, finite order and the prescribed decay), a profile $W:\mathbb R\to\mathbb C$, a real number $a$, complex parameters $u_0,c_P,s$, classes $a_0,s_P\in\mathbb Z/2$ and an integer $k$. Write $c_2:=P_2$'s central exponent and $\tilde w:=2s-c_P-c_2+1$, and recall $\mathrm{quasiChar}(u,\varepsilon,y)=|y|^u$ times $1$ if $\varepsilon=0$ and $\operatorname{sgn}(y)$ otherwise, $\mathrm{centralChar}(P_2,y)=\mathrm{quasiChar}(c_2,\varepsilon(P_2),y)$, and $\mathrm{diagOne}(y)=\mathrm{diag}(y,1)$. Assume $\operatorname{Re}\tilde w>-1$; assume (hIW) that for every $a_1\neq 0$ and $a_2>0$ the inner $(x,y_1,y_2)$-integrand displayed below is integrable on $\mathbb R\times\mathbb R\times(0,\infty)$ for Lebesgue measure restricted to $y_2>0$; and assume (hK4) that $a_2^{\tilde w}e^{-\pi a_2^2q^2}$ times the $(t,q,p)$-integrand of the right-hand side, but with the exponent of $|q|$ replaced by $u_0+1$, is integrable on $(0,\infty)\times\mathbb R\times\mathbb R\times(0,\infty)$. Then the iterated integral over $a_2\in(0,\infty)$ and $a_1\in\mathbb R$ of the expression which vanishes unless $a_1\neq0$ and $a_2>0$ and otherwise equals $$|a_1a_2|\,\Bigl(i^{k}\,|{-}a_1^{-1}|^{c_P+1}\bigl((-a_1^{-1})/|{-}a_1^{-1}|\bigr)^{s_P}W(-a_1/a_2)\Bigr)\,\mathrm{quasiChar}(u_0+1,a_0,-(a_1a_2)^{-1})\,|a_1a_2|^{s-1/2}a_1^{-2}$$ times $2\pi$ times the triple integral $\int_{y_1}\int_{y_2>0}\int_x$ of $$e^{-\pi(a_2^{-2}(x^2/y_1^2+y_2^{-2})+y_1^{-2})}\,a_1^2|y_1y_2|\Bigl(ia\,a_1\tfrac{y_2}{y_1}+ia_2^{-1}(y_1y_2)^{-1}\Bigr)e^{-\pi a^2a_1^2y_2^2}\,\mathrm{quasiChar}(u_0+2,a_0,(y_1y_2)^{-1})|y_1y_2|^{2}\,e^{2\pi i a x}\,\mathrm{centralChar}(P_2,y_2)|y_2|\,D.W(\mathrm{diagOne}(ay_1/y_2))\,y_2^2|y_1y_2|^{-4},$$ equals $2\pi\,i^{k}\,i\cdot\tfrac12\Gamma_{\mathbb R}(\tilde w+1)$ times $$\int_{t\in\mathbb R}\int_{q\in\mathbb R}\int_{p>0}\Sigma(t,q)\,W(-t)(a+tp^2)\,D.W\bigl(\mathrm{diagOne}(a|t|p/q)\bigr)|t|^{s-5/2-c_P-c_2}|q|^{u_0+c_P+c_2-2s-1}p^{u_0-c_2-3}e^{-\pi t^2p^2}e^{-\pi a^2/p^2}e^{-\pi a^2/q^2},$$ where $\Sigma(t,q)$ is the product of the five sign factors $\mathrm{quasiChar}(0,s_P,-t)$, $\mathrm{quasiChar}(0,a_0,-t)$, $\mathrm{quasiChar}(0,1,t)$, $\mathrm{quasiChar}(0,1,q)$, $\mathrm{quasiChar}(0,a_0,q)$.
--
--   This is the second step of the archimedean computation of the dual torus pairing attached to the minor section: the Iwasawa-unfolded four-fold integral is reduced, by performing the $a_2$-integral against a Gaussian and substituting torus coordinates, to an explicit $\Gamma_{\mathbb R}$-factor times a three-variable torus integral. It combines the fibrewise identity `dualTorusPair_iwasawa_fibre_eq_const_mul_integral_torusQuadruple_minor` with the general Gamma-integration lemma `setIntegral_integral_dite_eq_const_mul_GammaR_mul_integral_triple_of_fibre`, and feeds the weight-one root-number evaluation used in the Rankin–Selberg input to the converse theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_dualTorusPair_iwasawa_eq_const_mul_integral_torusTriple_minor_of_re_gt.lean

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

theorem LanglandsTunnell.Converse.dualTorusPair_iwasawa_eq_const_mul_integral_torusTriple_minor_of_re_gt
    {P₂ : RealArchParam} (D : ArchDatumR P₂) (W : ℝ → ℂ) (a : ℝ) (u₀ cP : ℂ) (a₀ sP : ZMod 2) (k : ℤ) (s : ℂ)
    (hw : -1 < (2 * s - cP - P₂.centralExponent + 1).re)
    (hIW : ∀ a₁ : ℝ, a₁ ≠ 0 → ∀ a₂ : ℝ, 0 < a₂ → Integrable (fun q : ℝ × ℝ × ℝ =>
        ((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (q.1 ^ 2 / q.2.1 ^ 2 + 1 / q.2.2 ^ 2) + 1 / q.2.1 ^ 2))) : ℂ) *
            (((a₁ ^ 2 * |q.2.1 * q.2.2| : ℝ)) : ℂ) *
            (-Complex.I * (a : ℂ) * (a₁ : ℂ) * ((-(q.2.2 / q.2.1) : ℝ) : ℂ) + Complex.I * (a₂⁻¹ : ℂ) * (((q.2.1 * q.2.2)⁻¹ : ℝ) : ℂ)) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * q.2.2 ^ 2)) : ℂ)) *
          (ArchR.quasiChar (u₀ + 2) a₀ (q.2.1 * q.2.2)⁻¹ * (((|(q.2.1 * q.2.2)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ)) *
          (ArchR.psi (a * q.1) * (ArchR.centralChar P₂ q.2.2 * ((|q.2.2| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * q.2.1 / q.2.2))) *
          ((q.2.2 ^ 2 * (|q.2.1 * q.2.2| ^ 4)⁻¹ : ℝ) : ℂ)) ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))))
    (hK4 : Integrable (fun r : ℝ × ℝ × ℝ × ℝ =>
        (((r.1 : ℝ) : ℂ) ^ (2 * s - cP - P₂.centralExponent + 1) * (Real.exp (-(Real.pi * r.1 ^ 2 * r.2.2.1 ^ 2)) : ℂ)) *
        ((ArchR.quasiChar 0 sP (-r.2.1) * ArchR.quasiChar 0 a₀ (-r.2.1) * ArchR.quasiChar 0 1 r.2.1 * ArchR.quasiChar 0 1 r.2.2.1 * ArchR.quasiChar 0 a₀ r.2.2.1) *
          (W (-r.2.1) * ((a : ℂ) + (r.2.1 : ℂ) * (r.2.2.2 : ℂ) ^ 2) * D.W (ArchR.diagOne (a * |r.2.1| * r.2.2.2 / r.2.2.1))) *
          ((((|r.2.1| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|r.2.2.1| : ℝ) : ℂ) ^ (u₀ + 1)) *
            (((r.2.2.2 : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * r.2.1 ^ 2 * r.2.2.2 ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / r.2.2.2 ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / r.2.2.1 ^ 2)) : ℂ)))) (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))))) :
    (∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ,
              if ha : a₁ ≠ 0 ∧ 0 < a₂ then
                ((((|a₁ * a₂| : ℝ) : ℂ) *
                    (Complex.I ^ (k : ℤ) *
                      ((((|(-a₁⁻¹ : ℝ)| : ℝ) : ℂ) ^ (cP + 1)) *
                        ((((-a₁⁻¹ : ℝ)) : ℂ) / ((|(-a₁⁻¹ : ℝ)| : ℝ) : ℂ)) ^ (sP.val : ℤ)) *
                      W (-a₁ / a₂))) *
                  (ArchR.quasiChar (u₀ + 1) a₀ (-(a₁ * a₂)⁻¹) *
                    (((2 * Real.pi : ℝ) : ℂ) * ∫ y₁ : ℝ, ∫ y₂ in Set.Ioi (0 : ℝ), ∫ x : ℝ,
          ((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (x ^ 2 / y₁ ^ 2 + 1 / y₂ ^ 2) + 1 / y₁ ^ 2))) : ℂ) *
            (((a₁ ^ 2 * |y₁ * y₂| : ℝ)) : ℂ) *
            (-Complex.I * (a : ℂ) * (a₁ : ℂ) * ((-(y₂ / y₁) : ℝ) : ℂ) + Complex.I * (a₂⁻¹ : ℂ) * (((y₁ * y₂)⁻¹ : ℝ) : ℂ)) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * y₂ ^ 2)) : ℂ)) *
          (ArchR.quasiChar (u₀ + 2) a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ)) *
          (ArchR.psi (a * x) * (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * y₁ / y₂))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ))) *
                  (((|a₁ * a₂| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
              else 0)
      = (((2 * Real.pi : ℝ) : ℂ) * Complex.I ^ (k : ℤ) * Complex.I * ((1 / 2 : ℂ) * Complex.Gammaℝ (2 * s - cP - P₂.centralExponent + 1 + 1))) *
        ∫ t : ℝ, ∫ q : ℝ, ∫ p in Set.Ioi (0 : ℝ),
          (ArchR.quasiChar 0 sP (-t) * ArchR.quasiChar 0 a₀ (-t) * ArchR.quasiChar 0 1 t * ArchR.quasiChar 0 1 q * ArchR.quasiChar 0 a₀ q) *
          (W (-t) * ((a : ℂ) + (t : ℂ) * (p : ℂ) ^ 2) * D.W (ArchR.diagOne (a * |t| * p / q))) *
          ((((|t| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|q| : ℝ) : ℂ) ^ (u₀ + cP + P₂.centralExponent - 2 * s - 1)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) : ℂ)) := by sorry
