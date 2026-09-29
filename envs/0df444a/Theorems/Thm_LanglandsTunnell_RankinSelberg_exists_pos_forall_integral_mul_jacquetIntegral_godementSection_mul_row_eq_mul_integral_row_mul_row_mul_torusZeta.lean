-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_pos_forall_integral_mul_jacquetIntegral_godementSection_mul_row_eq_mul_integral_row_mul_row_mul_torusZeta
-- name    : LanglandsTunnell.RankinSelberg.exists_pos_forall_integral_mul_jacquetIntegral_godementSection_mul_row_eq_mul_integral_row_mul_row_mul_torusZeta
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/012a810b-c06f-5df7-b4ec-3f77242cdd05
-- title:
--   Local Rankin–Selberg integral against a Godement section
-- statement:
--   Let $p$ be a nonzero prime of $\mathbb{Z}$ and $F=\mathbb{Q}_p$ the corresponding completion, with its Borel $\sigma$-algebras on $F$ and on $GL_2(F)$. The assertion is: for every Haar measure $\mu_2$ on $GL_2(F)$, every Haar measure $\mu_{N}$ on the image of $x\mapsto \begin{pmatrix}1&x\\0&1\end{pmatrix}$ in $GL_2(F)$, and every additive Haar measure $\nu$ on $F$, there is a real $c>0$ such that the following holds for all data: a locally constant $w\colon GL_2(F)\to\mathbb{C}$ with $w(n(x)g)=\psi_p(x)w(g)$, where $\psi_p$ is the standard local additive character and $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$; locally constant homomorphisms $\chi_0,\chi_1\colon F^\times\to\mathbb{C}^\times$; a locally constant compactly supported $\Phi_1$ on $F^2$; a function $f$ in the normalised principal series $I(\chi_0,\chi_1)$, i.e. $f$ locally constant, invariant under left translation by upper unipotents, and satisfying $f(\mathrm{diag}(a_0,a_1)g)=\chi_0(a_0)\chi_1(a_1)\,(\lVert a_0\rVert/\lVert a_1\rVert)^{1/2}f(g)$; the hypothesis that for each $g$ the function $t\mapsto \Phi_1(t\,e_2g)\chi_0(t)\chi_1(t)^{-1}\lvert t\rvert$ is integrable on $F^\times$ for the multiplicative measure obtained from the self-dual additive Haar measure at $p$ by dividing by the module and restricting to units, and that $f$ is the associated Godement section, $f(g)=\chi_0(\det g)\lvert\det g\rvert^{1/2}\int_{F^\times}\Phi_1(t\,e_2g)\chi_0(t)\chi_1(t)^{-1}\lvert t\rvert\,d^\times t$, where $e_2g$ is the second row of $g$; an element $w_0\in GL_2(F)$ with matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$; a locally constant $\Phi_2$ on $F^2$; and $s\in\mathbb{C}$. Assume that $g\mapsto w(g)f(w_0g)\Phi_2(e_2g)\lvert\det g\rvert^{s}$ is $\mu_2$-integrable, and that $g\mapsto \lVert \Phi_1(e_1g)\Phi_2(e_2g)\chi_0(\det g)\lvert\det g\rvert^{s+1/2}\rVert\cdot\int_{F^\times}\lVert w(\mathrm{diag}(y,1)g)\chi_1(y)\lvert y\rvert^{s-1/2}\rVert\,d^\times y$ is $\mu_2$-integrable. Then the function $g\mapsto w(g)\bigl(\int_F f(w_0n(y)g)\psi_p(y)\,d\nu(y)\bigr)\Phi_2(e_2g)\lvert\det g\rvert^{s}$ is integrable for $\mu_2$ weighted by the density attached to the unipotent subgroup and $\mu_N$; the function $g\mapsto \Phi_1(e_1g)\Phi_2(e_2g)\chi_0(\det g)\lvert\det g\rvert^{s+1/2}\int_{F^\times}w(\mathrm{diag}(y,1)g)\chi_1(y)\lvert y\rvert^{s-1/2}\,d^\times y$ is $\mu_2$-integrable; and the integral of the first against the weighted measure equals $c\,\chi_0(-1)$ times the $\mu_2$-integral of the second. Here $\lvert\cdot\rvert$ denotes the module of $F$, which agrees with the norm, and $e_1g$, $e_2g$ are the first and second rows of $g$; the constant $c$ depends only on $p$ and on the three measures, not on $w$, $\chi$, $\Phi_1$, $\Phi_2$, $f$, $w_0$ or $s$.
--
--   This is the local $GL_2\times GL_2$ Rankin–Selberg identity at a finite place in the case where one of the two factors is a principal series realised by a Godement section: the unipotent-quotient integral of $w$ against the Whittaker integral of the section is rewritten, up to a positive constant and the sign $\chi_0(-1)$, as an integral over $GL_2(F)$ of the Godement datum $\Phi_1$, the partner datum $\Phi_2$ and the $GL_2\times GL_1$ torus zeta integral of $w$ twisted by $\chi_1$, so that the section itself disappears from the formula. It feeds the two derivations of the Laurent functional equation for the local Rankin–Selberg integrals of principal series, in the Borel-eigenfunctional and the cuspidal case, within the Langlands–Tunnell part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_pos_forall_integral_mul_jacquetIntegral_godementSection_mul_row_eq_mul_integral_row_mul_row_mul_torusZeta.lean

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

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal
  LanglandsTunnell.CubicInduction
open NumberField.AdelicLevel (diagOne)

theorem LanglandsTunnell.RankinSelberg.exists_pos_forall_integral_mul_jacquetIntegral_godementSection_mul_row_eq_mul_integral_row_mul_row_mul_torusZeta
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure]
      (ν : Measure (p.adicCompletion ℚ)) [ν.IsAddHaarMeasure],
    ∃ c : ℝ, 0 < c ∧
      ∀ (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (_hwlc : IsLocallyConstant w)
        (_hwlaw : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
          w (unipotentGL2 x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g)
        (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
        (_hχ : ∀ i, IsLocallyConstant (χ i))

        (Φ₁ : (Fin 2 → p.adicCompletion ℚ) → ℂ) (_hΦ₁ : IsLocallyConstant Φ₁ ∧ HasCompactSupport Φ₁)
        (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (_hf : f ∈ principalSeries2 p χ)
        (_hfΦ₁ : ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
          Integrable (fun t : (p.adicCompletion ℚ)ˣ => Φ₁ (fun j : Fin 2 => (t : p.adicCompletion ℚ) * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 j) * ((χ 0 t : ℂˣ) : ℂ) * (((χ 1 t : ℂˣ) : ℂ))⁻¹ * ((modulus (t : p.adicCompletion ℚ) : ℝ) : ℂ)) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
          f g = ((χ 0 (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
            ∫ t : (p.adicCompletion ℚ)ˣ, Φ₁ (fun j : Fin 2 => (t : p.adicCompletion ℚ) * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 j) * ((χ 0 t : ℂˣ) : ℂ) * (((χ 1 t : ℂˣ) : ℂ))⁻¹ * ((modulus (t : p.adicCompletion ℚ) : ℝ) : ℂ) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))))
        (w₀ : GL (Fin 2) (p.adicCompletion ℚ))
        (_hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
        (Φ₂ : (Fin 2 → p.adicCompletion ℚ) → ℂ) (_hΦ₂ : IsLocallyConstant Φ₂)
        (s : ℂ),

        Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            w g * f (w₀ * g) * Φ₂ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s) μ₂ →

        Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            ‖Φ₁ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0) * Φ₂ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1) * ((χ 0 (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2)‖ *
              ∫ y : (p.adicCompletion ℚ)ˣ,
                ‖w (diagOne y * g) * ((χ 1 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)‖
                ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) μ₂ →
        Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            (w g * (∫ y, f (w₀ * unipotentGL2 y * g) * NumberField.StandardAddChar.psiLocal ℚ p y ∂ν) *
                Φ₂ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1)) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s)
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) ∧
        Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            Φ₁ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0) * Φ₂ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1) * ((χ 0 (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2) *
              ∫ y : (p.adicCompletion ℚ)ˣ,
                w (diagOne y * g) * ((χ 1 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
                ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) μ₂ ∧
        ∫ g, (w g * (∫ y, f (w₀ * unipotentGL2 y * g) * NumberField.StandardAddChar.psiLocal ℚ p y ∂ν) *
              Φ₂ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1)) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s
          ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) =
        c * ((χ 0 (-1) : ℂˣ) : ℂ) *
          ∫ g, Φ₁ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0) * Φ₂ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1) * ((χ 0 (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2) *
              (∫ y : (p.adicCompletion ℚ)ˣ,
                w (diagOne y * g) * ((χ 1 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
                ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∂μ₂ := by sorry
