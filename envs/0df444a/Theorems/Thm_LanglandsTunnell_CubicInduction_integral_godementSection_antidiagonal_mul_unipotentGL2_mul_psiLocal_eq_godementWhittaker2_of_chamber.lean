-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_integral_godementSection_antidiagonal_mul_unipotentGL2_mul_psiLocal_eq_godementWhittaker2_of_chamber
-- name    : LanglandsTunnell.CubicInduction.integral_godementSection_antidiagonal_mul_unipotentGL2_mul_psiLocal_eq_godementWhittaker2_of_chamber
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/4a6a9aa7-7336-5e4b-87dc-b713f152f784
-- title:
--   Jacquet integral of a Godement section on GL₂(ℚₚ)
-- statement:
--   Fix a finite place $p$ of $\mathbb{Q}$, write $F = \mathbb{Q}_p$ for the completion of $\mathbb{Q}$ at $p$, and let $d^\times t$ denote the measure on $F^\times$ obtained by pulling back along $t \mapsto t$ the measure $\mathrm{mulMeasure}$ of the self-dual additive Haar measure at $p$, i.e. the restriction of the latter to $F \setminus \{0\}$ with density $\mathrm{modulus}(x)^{-1} = \|x\|^{-1}$; here the self-dual measure is the Haar measure giving $\mathcal{O}_F$ mass $(\mathrm{absNorm}\,p)^{-\mathrm{level}(\psi_p)/2}$, $\psi_p$ being the local component at $p$ of the standard adelic additive character. Let $\chi_0, \chi_1 : F^\times \to \mathbb{C}^\times$ be locally constant homomorphisms with $|\chi_i(a)| = \|a\|^{\sigma_i}$ for reals $\sigma_1 < \sigma_0$, let $\Phi_1 : F^2 \to \mathbb{C}$ be locally constant of compact support, and let $f : \mathrm{GL}_2(F) \to \mathbb{C}$ satisfy, for every $g$, that $t \mapsto \Phi_1(t\,e_2 g)\,\chi_0(t)\chi_1(t)^{-1}\|t\|$ is $d^\times t$-integrable and that $f(g) = \chi_0(\det g)\,\|\det g\|^{1/2}\int_{F^\times} \Phi_1(t\,e_2 g)\,\chi_0(t)\chi_1(t)^{-1}\|t\|\,d^\times t$, where $e_2 g$ is the second row of $g$. Let $w_0 \in \mathrm{GL}_2(F)$ have matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ and write $n(y) = \begin{pmatrix}1&y\\0&1\end{pmatrix}$. Then, $F$ carrying its Borel $\sigma$-algebra, for every additive Haar measure $\nu$ on $F$ and every $g \in \mathrm{GL}_2(F)$ the function $y \mapsto f(w_0 n(y) g)\,\psi_p(y)$ is $\nu$-integrable and $$\int_F f(w_0 n(y) g)\,\psi_p(y)\,d\nu(y) = \chi_0(-1)\,\chi_0(\det g)\,\|\det g\|^{1/2}\int_{F^\times}\Bigl(\int_F \Phi_1(t\,e_1 g + y\,e_2 g)\,\psi_p(t^{-1}y)\,d\nu(y)\Bigr)\chi_0(t)\chi_1(t)^{-1}\,d^\times t,$$ with $e_1 g$ the first row of $g$; note the absence of the factor $\|t\|$ in the outer integrand on the right.
--
--   This is the local computation identifying the Jacquet (Whittaker) integral of a Godement section attached to $\Phi_1$ and the pair $(\chi_0,\chi_1)$ with $\chi_0(-1)$ times the partial Fourier transform of $\Phi_1$ in its second variable, valid in the chamber $\sigma_1 < \sigma_0$ where the defining zeta integral converges. It is used in the local Rankin–Selberg computations establishing the Laurent functional equation for the $(2,2)$ local integrals, both in the principal-series and in the cuspidal case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_integral_godementSection_antidiagonal_mul_unipotentGL2_mul_psiLocal_eq_godementWhittaker2_of_chamber.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_HaarQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm
open LanglandsTunnell.TateLocal
open LanglandsTunnell.CubicInduction

open NumberField.AdelicLevel (diagOne)

theorem LanglandsTunnell.CubicInduction.integral_godementSection_antidiagonal_mul_unipotentGL2_mul_psiLocal_eq_godementWhittaker2_of_chamber
    (p : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hχ : ∀ i, IsLocallyConstant (χ i))
    (σ : Fin 2 → ℝ)
    (hσ : ∀ (i : Fin 2) (a : (p.adicCompletion ℚ)ˣ), ‖((χ i a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (σ i))
    (h01 : σ 1 < σ 0)
    (Φ₁ : (Fin 2 → p.adicCompletion ℚ) → ℂ) (hΦ₁ : IsLocallyConstant Φ₁ ∧ HasCompactSupport Φ₁)
    (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hfΦ₁ : letI := localBorel ℚ p
      ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
        Integrable (fun t : (p.adicCompletion ℚ)ˣ => Φ₁ (fun j : Fin 2 => (t : p.adicCompletion ℚ) * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 j) * ((χ 0 t : ℂˣ) : ℂ) * (((χ 1 t : ℂˣ) : ℂ))⁻¹ * ((modulus (t : p.adicCompletion ℚ) : ℝ) : ℂ)) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
        f g = ((χ 0 (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
          ∫ t : (p.adicCompletion ℚ)ˣ, Φ₁ (fun j : Fin 2 => (t : p.adicCompletion ℚ) * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 j) * ((χ 0 t : ℂˣ) : ℂ) * (((χ 1 t : ℂˣ) : ℂ))⁻¹ * ((modulus (t : p.adicCompletion ℚ) : ℝ) : ℂ) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))))
    (w₀ : GL (Fin 2) (p.adicCompletion ℚ))
    (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0]) :
    letI := localBorel ℚ p
    ∀ (ν : Measure (p.adicCompletion ℚ)) [ν.IsAddHaarMeasure] (g : GL (Fin 2) (p.adicCompletion ℚ)),
      Integrable (fun y : p.adicCompletion ℚ => f (w₀ * unipotentGL2 y * g) * NumberField.StandardAddChar.psiLocal ℚ p y) ν ∧
      ∫ y, f (w₀ * unipotentGL2 y * g) * NumberField.StandardAddChar.psiLocal ℚ p y ∂ν =
        ((χ 0 (-1) : ℂˣ) : ℂ) *
          (((χ 0 (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
          ∫ t : (p.adicCompletion ℚ)ˣ,
            (∫ y : p.adicCompletion ℚ, Φ₁ (fun j : Fin 2 => (t : p.adicCompletion ℚ) * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 j + y * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 j) *
                NumberField.StandardAddChar.psiLocal ℚ p ((t : p.adicCompletion ℚ)⁻¹ * y) ∂ν) *
              ((χ 0 t : ℂˣ) : ℂ) * (((χ 1 t : ℂˣ) : ℂ))⁻¹ ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) := by sorry
