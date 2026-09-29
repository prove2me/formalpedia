-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_pos_forall_integral_weightedGodementWhittaker2_mul_row_eq_mul_integral_row_mul_row_mul_weightedTorusZeta
-- name    : LanglandsTunnell.RankinSelberg.exists_pos_forall_integral_weightedGodementWhittaker2_mul_row_eq_mul_integral_row_mul_row_mul_weightedTorusZeta
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/5decf2fe-4480-5996-919e-e258aabe3aef
-- title:
--   Weighted Whittaker unfolding of a local GL₂ zeta integral
-- statement:
--   Let $p$ be a nonzero prime of $\mathcal O_{\mathbb Q}$ and write $F$ for the completion $\mathbb Q_p$ at $p$, equipped with its Borel structures on $F$ and on $GL_2(F)$. The assertion is: for every Haar measure $\mu_2$ on $GL_2(F)$, every Haar measure $\mu_{N}$ on the image of $x \mapsto \begin{pmatrix}1&x\\0&1\end{pmatrix}$ in $GL_2(F)$, and every additive Haar measure $\nu$ on $F$, there is a real $c>0$ such that the following holds for all data: a locally constant $w : GL_2(F)\to\mathbb C$ with $w(\begin{pmatrix}1&x\\0&1\end{pmatrix}g)=\psi_p(x)\,w(g)$, where $\psi_p$ is the local component at $p$ of the standard adelic additive character; a pair $\chi_0,\chi_1$ of locally constant homomorphisms $F^\times\to\mathbb C^\times$; a locally constant compactly supported $\Phi_1$ on $F^2$; a locally constant $\Phi_2$ on $F^2$; an arbitrary function $\omega$ on $\Gamma_0\times\Gamma_0$, $\Gamma_0 = \mathbb Z\cup\{0\}$ written multiplicatively as the value monoid of $F$; and $s\in\mathbb C$. Throughout, $|a|$ denotes $\mathrm{modulus}(a)$, the module of the scaling action of $a$ on additive Haar measure (equal to $\|a\|$), $d^\times t$ denotes the multiplicative Haar measure obtained from the self-dual additive measure on $F$ by restricting to $F\setminus\{0\}$, multiplying by $|x|^{-1}$ and pulling back along $F^\times\to F$, and $v$ the valuation. Suppose that $$(g,y)\mapsto \Phi_1(e_1g)\Phi_2(e_2g)\chi_0(\det g)|\det g|^{s+1/2}\,\omega(v(y),v(\det g))\,w(\mathrm{diag}(y,1)g)\,\chi_1(y)|y|^{s-1/2}$$ is integrable on $GL_2(F)\times F^\times$ for $\mu_2\otimes d^\times y$, where $e_1g,e_2g$ are the two rows of $g$. Then the function $$h\mapsto \chi_0(\det h)|\det h|^{1/2}\Bigl(\int_{F^\times}\omega\bigl(v(t)^{-1},v(t)v(\det h)\bigr)\Bigl(\int_F\Phi_1(t\,e_1h+y\,e_2h)\,\psi_p(t^{-1}y)\,d\nu(y)\Bigr)\chi_0(t)\chi_1(t)^{-1}d^\times t\Bigr)\,w(h)\Phi_2(e_2h)\,|\det h|^{s}$$ is integrable against $\mu_2$ weighted by the density [`HaarQuotient.density`](def/HaarQuotient.html#L25) of the unipotent subgroup relative to $\mu_N$ (the realisation of integration over $N\backslash GL_2(F)$), and its integral against that weighted measure equals $c$ times $$\int_{GL_2(F)}\Phi_1(e_1g)\Phi_2(e_2g)\chi_0(\det g)|\det g|^{s+1/2}\Bigl(\int_{F^\times}\omega(v(y),v(\det g))\,w(\mathrm{diag}(y,1)g)\,\chi_1(y)|y|^{s-1/2}d^\times y\Bigr)d\mu_2(g).$$ The constant $c$ is uniform in $w$, $\chi$, $\Phi_1,\Phi_2$, $\omega$ and $s$, depending only on the chosen measures.
--
--   This is the unfolding identity relating a Godement–Jacquet-shape zeta integral over $GL_2(F)\times F^\times$ to the integral over $N\backslash GL_2(F)$ of the partial-Fourier Whittaker function attached to $\Phi_1$, here in a form carrying an arbitrary weight $\omega$ in the valuations of $y$ and $\det g$ and with no positivity or chamber restriction on the characters. It is used in the local analysis of Rankin–Selberg integrals at a finite place, in establishing the Laurent functional equation for such integrals for principal series and for cuspidal data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_pos_forall_integral_weightedGodementWhittaker2_mul_row_eq_mul_integral_row_mul_row_mul_weightedTorusZeta.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_HaarQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal
  LanglandsTunnell.CubicInduction
open NumberField.AdelicLevel (diagOne)

theorem LanglandsTunnell.RankinSelberg.exists_pos_forall_integral_weightedGodementWhittaker2_mul_row_eq_mul_integral_row_mul_row_mul_weightedTorusZeta
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
        (Φ₂ : (Fin 2 → p.adicCompletion ℚ) → ℂ) (_hΦ₂ : IsLocallyConstant Φ₂)
        (ω : WithZero (Multiplicative ℤ) → WithZero (Multiplicative ℤ) → ℂ)
        (s : ℂ),

        Integrable (fun q : GL (Fin 2) (p.adicCompletion ℚ) × (p.adicCompletion ℚ)ˣ =>
            Φ₁ ((q.1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0) * Φ₂ ((q.1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1) *
                ((χ 0 (Matrix.GeneralLinearGroup.det q.1) : ℂˣ) : ℂ) *
                ((modulus ((Matrix.GeneralLinearGroup.det q.1 : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2) *
              (ω (Valued.v (q.2 : p.adicCompletion ℚ)) (Valued.v ((Matrix.GeneralLinearGroup.det q.1 : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)) *
                w (diagOne q.2 * q.1) * ((χ 1 q.2 : ℂˣ) : ℂ) * ((modulus (q.2 : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)))
          (μ₂.prod (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) →
        Integrable (fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
            (((χ 0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
              ∫ t : (p.adicCompletion ℚ)ˣ,
                ω (Valued.v (t : p.adicCompletion ℚ))⁻¹ (Valued.v (t : p.adicCompletion ℚ) * Valued.v ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)) *
                  (∫ y : p.adicCompletion ℚ, Φ₁ (fun j : Fin 2 => (t : p.adicCompletion ℚ) * (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 j + y * (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 j) *
                      NumberField.StandardAddChar.psiLocal ℚ p ((t : p.adicCompletion ℚ)⁻¹ * y) ∂ν) *
                  ((χ 0 t : ℂˣ) : ℂ) * (((χ 1 t : ℂˣ) : ℂ))⁻¹ ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) *
              (w h * Φ₂ ((h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1)) *
              ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s)
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) ∧
        ∫ h, (fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
            (((χ 0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
              ∫ t : (p.adicCompletion ℚ)ˣ,
                ω (Valued.v (t : p.adicCompletion ℚ))⁻¹ (Valued.v (t : p.adicCompletion ℚ) * Valued.v ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)) *
                  (∫ y : p.adicCompletion ℚ, Φ₁ (fun j : Fin 2 => (t : p.adicCompletion ℚ) * (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 j + y * (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 j) *
                      NumberField.StandardAddChar.psiLocal ℚ p ((t : p.adicCompletion ℚ)⁻¹ * y) ∂ν) *
                  ((χ 0 t : ℂˣ) : ℂ) * (((χ 1 t : ℂˣ) : ℂ))⁻¹ ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) *
              (w h * Φ₂ ((h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1)) *
              ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s) h
          ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) =
        c *
          ∫ g, Φ₁ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0) * Φ₂ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1) * ((χ 0 (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2) *
              (∫ y : (p.adicCompletion ℚ)ˣ,
                ω (Valued.v (y : p.adicCompletion ℚ)) (Valued.v ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)) *
                  w (diagOne y * g) * ((χ 1 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
                ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∂μ₂ := by sorry
