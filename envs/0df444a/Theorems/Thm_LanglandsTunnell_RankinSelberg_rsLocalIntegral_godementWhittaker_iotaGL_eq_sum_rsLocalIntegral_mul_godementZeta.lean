-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_rsLocalIntegral_godementWhittaker_iotaGL_eq_sum_rsLocalIntegral_mul_godementZeta
-- name    : LanglandsTunnell.RankinSelberg.rsLocalIntegral_godementWhittaker_iotaGL_eq_sum_rsLocalIntegral_mul_godementZeta
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/4a2d469a-f06f-5689-a602-049bb25cfce3
-- title:
--   Unfolding of a Godement-section Rankin–Selberg local integral
-- statement:
--   Fix a nonzero prime $p$ of $\mathcal O_{\mathbb Q}$ and write $F = \mathbb Q_p$ for the completion, $\psi =$ `psiLocal ℚ p` for the $p$-component of the standard adelic additive character, $|a| =$ `modulus` $a$ for the module of $a \in F$ (the distributive Haar character of $a$ when $a \neq 0$, and $0$ at $0$), and $N$ for the image of `unipotentGL2Hom`, i.e. the group of matrices $\begin{pmatrix}1&x\\0&1\end{pmatrix}$. Given a homomorphism $\chi : F^\times \to \mathbb C^\times$, locally constant functions $\varphi_1$ on $M_2(F)$, $\varphi_2$ on $F^2$ and $W_1, w$ on $GL_2(F)$ with $W_1(n(x)g) = \psi(-x)W_1(g)$ and $w(n(x)g) = \psi(x)w(g)$ for all $x \in F$, $g \in GL_2(F)$, an open compact subgroup $\Omega \le GL_2(F)$ with $\varphi_1(\omega h) = \varphi_1(h)$ and $\chi(\det \omega) = 1$ for $\omega \in \Omega$, and finite families $(w_j)_{j \in \iota}$, $(c_j)_{j \in \iota}$ of locally constant functions on $GL_2(F)$, the assertion is the following, with $GL_2(F)$ and $F$ carrying their Borel structures. Let $\mu_2$ and $\nu$ be Haar measures on $GL_2(F)$ and $\mu_{N}$ a Haar measure on $N$, and suppose $\int_\Omega w(g\omega h)\,d\nu(\omega) = \nu(\Omega)\sum_j c_j(h)w_j(g)$ for all $g,h$. Let $s \in \mathbb C$, and assume three integrability hypotheses: that $(g,h) \mapsto \bigl(\varphi_1(h)\chi(\det h)|\det h|^{s+1/2}\bigr)\bigl(W_1(g)w(gh)\varphi_2(g_{10},g_{11})|\det g|^{s}\bigr)$ is integrable for the product of $\nu$ with $\mu_2$ weighted by the density [`HaarQuotient.density`](def/HaarQuotient.html#L25) of $N$ with $\mu_N$, and that for each $j$ the two factors $g \mapsto W_1(g)w_j(g)\varphi_2(g_{10},g_{11})|\det g|^{s+1/2-1/2}$ and $h \mapsto c_j(h)\varphi_1(h)\chi(\det h)|\det h|^{s+1/2}$ are integrable for the weighted measure and for $\nu$ respectively. Then the Rankin–Selberg local integral [`RSCarrier.rsLocalIntegral`](def/LanglandsTunnell_RSCarrier.html#L16) taken with $\mu_2$, $N$, $\mu_N$, the modulus $\delta(g) = |\det g|$, parameter $s$, the Whittaker function $$W(g) = \chi(\det g)\,|\det g| \int_{GL_2(F)} \varphi_1(hg)\,\varphi_2\bigl((h^{-1})_{10},(h^{-1})_{11}\bigr)\,W_1(h^{-1})\,\chi(\det h)\,|\det h|^{1/2}\,d\nu(h)$$ and the second function $w$ — that is, $\int W(g)w(g)|\det g|^{s-1/2}$ against $\mu_2$ weighted by the density — equals $\sum_j$ of the same local integral at parameter $s+1/2$ with $W_1$ and $g \mapsto w_j(g)\varphi_2(g_{10},g_{11})$, each multiplied by $\int_{GL_2(F)} c_j(h)\varphi_1(h)\chi(\det h)|\det h|^{s+1/2}\,d\nu(h)$.
--
--   This is the Jacquet–Piatetski-Shapiro–Shalika unfolding of a $GL_3 \times GL_2$ Rankin–Selberg integral in the case where the $GL_3$ Whittaker function is the Godement-section Whittaker function of a pure tensor $\varphi_1 \otimes \varphi_2 \otimes W_1$ restricted to $\mathrm{diag}(g,1)$: the local integral is expressed as a finite sum of products of a $GL_2 \times GL_2$ local integral with a Godement–Jacquet zeta integral at $s + 1/2$. It feeds the construction of the $GL_3$ Whittaker functions used in the converse-theorem input for the Langlands–Tunnell step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_rsLocalIntegral_godementWhittaker_iotaGL_eq_sum_rsLocalIntegral_mul_godementZeta.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

theorem LanglandsTunnell.RankinSelberg.rsLocalIntegral_godementWhittaker_iotaGL_eq_sum_rsLocalIntegral_mul_godementZeta
    (p : HeightOneSpectrum (𝓞 ℚ))

    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ)

    (φ₁ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ₁ : IsLocallyConstant φ₁)
    (φ₂ : (p.adicCompletion ℚ) × (p.adicCompletion ℚ) → ℂ) (hφ₂ : IsLocallyConstant φ₂)
    (W₁ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hW₁ : IsLocallyConstant W₁)
    (hW₁law : ∀ (x : (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      W₁ (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p (-x) * W₁ g)

    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hw : IsLocallyConstant w)
    (hwlaw : ∀ (x : (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g)

    (Ω : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)))
    (hΩo : IsOpen (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))) (hΩc : IsCompact (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))))
    (hφ₁Ω : ∀ ω ∈ Ω, ∀ h : GL (Fin 2) (p.adicCompletion ℚ),
      φ₁ ((ω * h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = φ₁ ((h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)))
    (hχΩ : ∀ ω ∈ Ω, χ (Matrix.GeneralLinearGroup.det ω) = 1)

    (ι : Type) [Fintype ι]
    (wj : ι → GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hwj : ∀ j, IsLocallyConstant (wj j))
    (c : ι → GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hc : ∀ j, IsLocallyConstant (c j)) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := (p.adicCompletion ℚ))).range) [μN₂.IsHaarMeasure]
      (ν : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [ν.IsHaarMeasure],
    (∀ g h : GL (Fin 2) (p.adicCompletion ℚ),
        ∫ ω in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w (g * ω * h) ∂ν =
          ((ν (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ) * ∑ j, c j h * wj j g) →
    ∀ s : ℂ,

      Integrable (fun gh : GL (Fin 2) (p.adicCompletion ℚ) × GL (Fin 2) (p.adicCompletion ℚ) =>
          (φ₁ (gh.2 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det gh.2) : ℂˣ) : ℂ) *
              ((modulus ((Matrix.GeneralLinearGroup.det gh.2 : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2)) *
            (W₁ gh.1 * w (gh.1 * gh.2) *
              φ₂ ((gh.1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (gh.1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) *
              ((modulus ((Matrix.GeneralLinearGroup.det gh.1 : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ s))
        ((μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)).prod ν) →

      (∀ j, Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          (W₁ g * (wj j g * φ₂ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1))) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2))
        (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂))) →

      (∀ j, Integrable (fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
          c j h * φ₁ (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2)) ν) →

      RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ))
          s
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) *
              ∫ h : GL (Fin 2) (p.adicCompletion ℚ),
                φ₁ ((h * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
                  φ₂ (((h⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, ((h⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) *
                  W₁ h⁻¹ * ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
                  ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (1 / 2 : ℂ) ∂ν)
          w =
        ∑ j, RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ))
          (s + 1 / 2)
          W₁
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => wj j g * φ₂ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)) *
            ∫ h : GL (Fin 2) (p.adicCompletion ℚ),
              c j h * φ₁ (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
                ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2) ∂ν := by sorry
