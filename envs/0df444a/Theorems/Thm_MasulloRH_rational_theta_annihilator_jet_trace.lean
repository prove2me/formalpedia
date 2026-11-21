-- Prove2me | Theorems.Thm_MasulloRH_rational_theta_annihilator_jet_trace
-- name    : MasulloRH.rational_theta_annihilator_jet_trace
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T01:20:57.874683+00:00
-- url     : https://prove2.me/theorems/5f60b4c6-529b-4ae4-b047-0eb416d36470
-- title:
--   The rational theta annihilator is the critical-line jet space and carries its convolution trace
-- statement:
--   Let $w_p(x)=(1+x^2)^{-p/2}$ with $p>1/2$. For each complex Schwartz test $g$ on the real line with $g(0)=\int g=0$, form the rational theta profile $T_g(x)=e^{x/2}\sum_{n\in\mathbb Z}g(ne^x)$. Define $E_p\subset L^2(\mathbb R)$ by requiring $\int w_p^{-1}u\,T_g=0$ for every such $g$.
--
--   Then $E_p$ is exactly the closed span of $w_p(x)x^r e^{i\operatorname{Im}(\rho)x}$ for the critical-line zeros $\rho$ of $\zeta$ with $r<\operatorname{ord}_{\rho}\zeta$ and $r+1/2<p$. For every admissible rational trace test $\varphi$, the integrated translations
--   $$
--   A_{p,\varphi}u=\int_{\mathbb R}\varphi(e^y)\frac{w_p(\cdot)}{w_p(\cdot+y)}u(\cdot+y)\,dy
--   $$
--   act on $E_p$ and give a nuclear operator. With $d_p(\rho)=\min(\operatorname{ord}_\rho\zeta,\lceil p-1/2\rceil)$, the trace is the absolutely convergent sum
--   $$
--   \operatorname{Tr}(A_{p,\varphi})=\sum_{\Re\rho=1/2}d_p(\rho)\mathcal M\varphi(\rho-1/2).
--   $$
--   The Hilbert space in this statement is defined directly by all admissible rational real-place theta tests. The theorem is unconditional.
-- source:
--   A. Connes, Trace formula in noncommutative geometry and the zeros of the Riemann zeta function, Appendix I (14)–(38) and Corollary 2, https://arxiv.org/abs/math/9811068. A. M. Masullo, The Music of the Primes, §§10.2.1.1, 10.3.1, equations (10.2.1.7)–(10.2.1.10), (10.3.1.2)–(10.3.1.4). Rational real-place, norm-character, central-line model. Smooth spectral localization follows the repair proposed by Calvin Yost-Wolff in Prove2Me discussion d8680fb7-dd35-4a9c-ab4e-5888ec240d48.

import Mathlib
import Definitions.Def_MasulloRH_RationalThetaSpace
import Definitions.Def_MasulloRH_RationalTrace
import Definitions.Def_MasulloGRH_HilbertNuclear
open MasulloRH MasulloGRH MeasureTheory
open scoped InnerProductSpace

theorem MasulloRH.rational_theta_annihilator_jet_trace (p : ℝ) (hp : 1/2<p) :
    let Z := {ρ : ℂ // riemannZeta ρ = 0 ∧ ρ.re = 1/2}
    let H := Lp ℂ 2 (volume : Measure ℝ)
    rationalThetaAnnihilator p =
      (Submodule.span ℂ {u : H | ∃ (ρ : Z) (r : ℕ),
        r < analyticOrderNatAt riemannZeta ρ.val ∧ (r:ℝ)+1/2 < p ∧
        (u : ℝ→ℂ) =ᵐ[volume] fun x : ℝ => ((1+x^2)^(-p/2) : ℝ) *
          ((x:ℂ)^r * Complex.exp (↑(ρ.val.im*x)*Complex.I))}).topologicalClosure ∧
    ∀ (φ : ℝ → ℂ), IsRationalTraceTest φ →
      ∃! T : rationalThetaAnnihilator p →L[ℂ] rationalThetaAnnihilator p,
        IsRationalThetaConvolution p φ T ∧ IsNuclearOperator T ∧
          HasSum (fun ρ : Z =>
            ((min (analyticOrderNatAt riemannZeta ρ.val) ⌈p-1/2⌉₊ : ℕ) : ℂ) *
              mellin φ (ρ.val-1/2)) (operatorTrace T) := by sorry
