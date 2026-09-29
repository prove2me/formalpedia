-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_jacquetIntegral_mul_whittaker_mul_row_withDensity_of_admissible_of_chamber
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_integrable_jacquetIntegral_mul_whittaker_mul_row_withDensity_of_admissible_of_chamber
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/ee950b55-0bb4-53c8-b047-93144ef6b06c
-- title:
--   Half-plane integrability of the local GL₂timesGL₂ integrand
-- statement:
--   Fix a nonzero prime $p$ of the ring of integers of $\mathbb{Q}$, and work over the completion $F=\mathbb{Q}_p$ with its standard additive character `psiLocal` and the self-dual Haar measure `selfDualHaarAt`. Let $\mu=(\mu_0,\mu_1)$ be a pair of multiplicative characters $F^\times\to\mathbb{C}^\times$, each locally constant, let $\sigma_0,\sigma_1\in\mathbb{R}$ satisfy $\lvert\mu_i(a)\rvert=\lVert a\rVert^{\sigma_i}$ for all $a$, and assume $\sigma_1<\sigma_0$. Let $\varphi$ lie in `principalSeries2 p μ`, that is, $\varphi:\mathrm{GL}_2(F)\to\mathbb{C}$ is locally constant, invariant under left translation by the matrices $\begin{pmatrix}1&x\\0&1\end{pmatrix}$, and satisfies $\varphi(\mathrm{diag}(a_0,a_1)g)=\mathrm{torusChar2}\,p\,\mu\,a\cdot\mathrm{halfModulus2}\,p\,a\cdot\varphi(g)$. Let $\theta:F^\times\to\mathbb{C}^\times$ be a character and $w:\mathrm{GL}_2(F)\to\mathbb{C}$ a function with $w\bigl(\begin{pmatrix}1&a\\0&1\end{pmatrix}g\bigr)=\psi_p(a)w(g)$, right invariant under some open subgroup, with $w(zI\cdot g)=\theta(z)w(g)$, and admissible in the sense that for every open subgroup $U$ there is a finite set $B$ of functions such that every $U$-right-invariant element of the span of the right translates $g\mapsto w(gh)$ lies in the span of $B$. Let $\varphi_2:F\times F\to\mathbb{C}$ be locally constant with compact support. Then there exists $\sigma'\in\mathbb{R}$ such that for every Haar measure $\mu_2$ on $\mathrm{GL}_2(F)$ (with its Borel structure), every Haar measure $\mu_{N_2}$ on the range of `unipotentGL2Hom`, i.e. the subgroup of matrices $\begin{pmatrix}1&x\\0&1\end{pmatrix}$, and every $s\in\mathbb{C}$ with $\mathrm{Re}\,s>\sigma'$, the function $$g\mapsto\Bigl(\int_F\psi_p(x)\,\varphi\bigl(\begin{pmatrix}0&1\\1&0\end{pmatrix}\begin{pmatrix}1&x\\0&1\end{pmatrix}g\bigr)\,dx\Bigr)\,w(g)\,\varphi_2(g_{10},g_{11})\,\mathrm{modulus}(\det g)^{s+1/2-1/2}$$ is integrable for $\mu_2$ weighted by the quotient density [`HaarQuotient.density`](def/HaarQuotient.html#L25) of that unipotent subgroup relative to $\mu_{N_2}$, namely $g\mapsto \mathrm{weight}(g)/\int^-_{x}\mathrm{weight}(xg)\,d\mu_{N_2}$.
--
--   This is the absolute convergence, on a right half-plane in $s$, of the local Rankin–Selberg integral $\Psi(s,W',w,\varphi_2)$ for $\mathrm{GL}_2\times\mathrm{GL}_2$, where $W'$ is the Jacquet integral attached to a principal-series vector in the chamber $\sigma_1<\sigma_0$, realised on $N_2\backslash\mathrm{GL}_2(F)$ through the quotient-density measure. It feeds the Godement unfolding statement and supplies the integrability hypothesis in the local functional equation for principal-series partners.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_jacquetIntegral_mul_whittaker_mul_row_withDensity_of_admissible_of_chamber.lean

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

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open LanglandsTunnell.RankinSelberg

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

theorem LanglandsTunnell.RankinSelberg.exists_forall_integrable_jacquetIntegral_mul_whittaker_mul_row_withDensity_of_admissible_of_chamber
    (p : HeightOneSpectrum (𝓞 ℚ))

    (μ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hμ : ∀ i, IsLocallyConstant (μ i))
    (σ : Fin 2 → ℝ)
    (hσ : ∀ (i : Fin 2) (a : (p.adicCompletion ℚ)ˣ), ‖((μ i a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (σ i))
    (h01 : σ 1 < σ 0)
    (φ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ : φ ∈ principalSeries2 p μ)

    (θ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hwlaw : ∀ (a : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (unipotent a * g) = NumberField.StandardAddChar.psiLocal ℚ p a * w g)
    (hwsm : ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
      ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g)
    (hwadm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w' (g * k) = w' g) →
            w' ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hcentral : ∀ (zc : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (Matrix.GeneralLinearGroup.scalar (Fin 2) zc * g) = ((θ zc : ℂˣ) : ℂ) * w g)
    (φ₂ : (p.adicCompletion ℚ) × (p.adicCompletion ℚ) → ℂ) (hφ₂ : IsLocallyConstant φ₂ ∧ HasCompactSupport φ₂) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    ∃ σ' : ℝ, ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := (p.adicCompletion ℚ))).range) [μN₂.IsHaarMeasure] (s : ℂ), σ' < s.re →
        Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          ((fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              ∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
                φ (antidiagonal2 p * upperUnipotent2 p x * g) ∂(selfDualHaarAt ℚ p)) g *
            (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              w g * φ₂ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)) g) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)) := by sorry
