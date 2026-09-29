-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_exists_forall_integrable_thetaFree_iwasawaIntegrand_conjBlockPow_colHarmonic_of_oneSided_profile
-- name    : LanglandsTunnell.Converse.exists_forall_integrable_thetaFree_iwasawaIntegrand_conjBlockPow_colHarmonic_of_oneSided_profile
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/f1eb0b45-e68c-517d-aaba-0762c600b119
-- title:
--   Integrability of the θ-free Iwasawa integrand, one-sided profile
-- statement:
--   Let $W:\mathbb R\to\mathbb C$ and $Q\in\mathbb C$ satisfy $W(t)=2t^{Q}e^{-2\pi t}$ for $t>0$ and $W(t)=0$ for $t<0$; let $P_2$ be a real archimedean parameter (principal, with data $u_1,a_1,u_2,a_2$, or discrete, with data $u,k\ge 1$), let $D$ be an arbitrary real archimedean Whittaker datum for $P_2$ (a smooth $\mathbb C$-valued function $D.W$ on $2\times 2$ real matrices transforming by $\psi(x)=e^{2\pi i x}$ under the unipotent and by the central character under scalars, with entire zeta functions, functional equation, finite order and the stated decay at $0$ and $\infty$), let $a\neq0$ be real, let $u_0,c_P\in\mathbb C$, $a_0\in\mathbb Z/2$, $m,n\in\mathbb N$ and $\varepsilon'\in\mathbb R$. Then there is $\sigma\in\mathbb R$ such that for every $s$ with $\operatorname{Re}s>\sigma$ the function of $(x,y_1,y_2)\in\mathbb R^3$
--   $$\bigl(|y_1y_2|^{-u_0}\epsilon_{a_0}(y_1y_2)\bigr)\,|y_1y_2|^{2}\cdot\Bigl(|y_2|^{c_{P_2}}\epsilon_{P_2}(y_2)\,|y_2|\Bigr)\cdot\Bigl(\int_{\mathbb R}W(t)\,\psi(atx)\,D.W\bigl(\operatorname{diag}(aty_1/y_2,1)\bigr)\,|t|^{s-1/2}t^{-2}\,dt\Bigr)\cdot\Bigl(\tfrac1{y_1}-\tfrac1{y_2}+i\tfrac{x}{y_1}\Bigr)^{m}e^{-\pi\left(\frac{1+x^{2}}{y_1^{2}}+\frac1{y_2^{2}}\right)}|y_1y_2|\,(-ia)^{n}(\varepsilon' i y_2)^{n}\cdot\tfrac12(\pi a^{2}y_2^{2})^{-w/2}\Gamma(w/2)\cdot y_2^{2}|y_1y_2|^{-4},$$
--   where $c_{P_2}$ is the central exponent of $P_2$ ($u_1+u_2$, resp.\ $2u$), $\epsilon_{a_0}$ and $\epsilon_{P_2}$ are the sign factors attached to $a_0$ and to `P₂.centralSign` (equal to $1$ when the class is $0$ and to $\operatorname{sign}$ otherwise), and $w=c_P+c_{P_2}+2s+n+1$, is integrable for Lebesgue measure in $x$ and $y_1$ and Lebesgue measure restricted to $(0,\infty)$ in $y_2$.
--
--   This is the absolute-convergence input for the archimedean Rankin–Selberg computation in the converse-theorem route to Langlands–Tunnell: the integrand is the $\theta$-free Iwasawa-coordinate integrand of the unfolded torus pair, carrying a degree-$m$ conjugate block harmonic and a degree-$n$ column harmonic, with the inner $t$-integral kept inside. It is cited by [`LanglandsTunnell.RankinSelberg.exists_forall_iwasawaIntegral_eq_const_mul_oneSided_torusPair_add_mirror_of_discreteProfile_conjBlockHarmonic_colHarmonic`](thm.html#LanglandsTunnell.RankinSelberg.exists_forall_iwasawaIntegral_eq_const_mul_oneSided_torusPair_add_mirror_of_discreteProfile_conjBlockHarmonic_colHarmonic), where it licenses the interchange of integrations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_exists_forall_integrable_thetaFree_iwasawaIntegrand_conjBlockPow_colHarmonic_of_oneSided_profile.lean

import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Mathlib.Analysis.MellinTransform

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

theorem LanglandsTunnell.Converse.exists_forall_integrable_thetaFree_iwasawaIntegrand_conjBlockPow_colHarmonic_of_oneSided_profile
    (W : ℝ → ℂ) (Q : ℂ)
    (hWpos : ∀ t : ℝ, 0 < t → W t = (2 : ℂ) * (t : ℂ) ^ Q * (Real.exp (-(2 * Real.pi * t)) : ℂ))
    (hWneg : ∀ t : ℝ, t < 0 → W t = 0)
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (a : ℝ) (ha : a ≠ 0) (u₀ cP : ℂ) (a₀ : ZMod 2) (m n : ℕ) (ε' : ℝ) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Integrable (fun q : ℝ × ℝ × ℝ =>
        ArchR.quasiChar u₀ a₀ (q.2.1 * q.2.2)⁻¹ * (((|(q.2.1 * q.2.2)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          ((ArchR.centralChar P₂ q.2.2 * ((|q.2.2| : ℝ) : ℂ)) *
            (∫ t : ℝ, W t * ArchR.psi (a * t * q.1) * D.W (ArchR.diagOne (a * t * q.2.1 / q.2.2)) *
               (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
            (((((1 / q.2.1 - 1 / q.2.2 : ℝ) : ℂ)) + Complex.I * (((q.1 / q.2.1 : ℝ) : ℂ))) ^ m *
              (Real.exp (-(Real.pi * ((1 + q.1 ^ 2) / q.2.1 ^ 2 + 1 / q.2.2 ^ 2))) : ℂ) *
              ((|q.2.1 * q.2.2| : ℝ) : ℂ) *
              (-Complex.I * (a : ℂ)) ^ n * ((ε' : ℂ) * Complex.I * (q.2.2 : ℂ)) ^ n *
              ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * q.2.2 ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + n + 1) / 2)) *
                Complex.Gamma ((cP + P₂.centralExponent + 2 * s + n + 1) / 2)))) *
          ((q.2.2 ^ 2 * (|q.2.1 * q.2.2| ^ 4)⁻¹ : ℝ) : ℂ))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))) := by sorry
