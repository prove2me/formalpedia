-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_norm_jacquetIntegral_principalSeries2_diagUnits2_mul_le_and_eq_zero_of_chamber
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_norm_jacquetIntegral_principalSeries2_diagUnits2_mul_le_and_eq_zero_of_chamber
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/d411a367-9223-5d26-bee5-754953da6e37
-- title:
--   Gauge bound and far-out vanishing for a GL₂ Jacquet integral
-- statement:
--   Let $p$ be a height-one prime of the ring of integers of $\mathbb{Q}$, so that $\mathbb{Q}_p$ denotes the completion `p.adicCompletion ℚ`. Let $\mu_0,\mu_1$ be homomorphisms $\mathbb{Q}_p^\times \to \mathbb{C}^\times$, each locally constant as a function, and let $\sigma_0,\sigma_1$ be reals with $\|\mu_i(a)\| = \|a\|^{\sigma_i}$ for all $a$, and with $\sigma_1 < \sigma_0$. Let $\varphi : \mathrm{GL}_2(\mathbb{Q}_p)\to\mathbb{C}$ lie in `principalSeries2 p μ`, i.e. $\varphi$ is locally constant, invariant under left translation by the unipotent matrices $\binom{1\ x}{0\ 1}$, and satisfies $\varphi(\mathrm{diag}(a_0,a_1)g) = \mu_0(a_0)\mu_1(a_1)\sqrt{\|a_0\|/\|a_1\|}\,\varphi(g)$. Then, for the Borel measurable structures on $\mathrm{GL}_2(\mathbb{Q}_p)$ and on $\mathbb{Q}_p$, there are a real $C \ge 0$ and an integer $M_1$ such that for every $k$ in [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤`](def/AdelicDock_LocalEmbedding.html#L178) (the elements of $\mathrm{GL}_2(\mathbb{Q}_p)$ whose image under the embedding into $\mathrm{GL}_2$ of the finite adeles lies in the level-one adelic subgroup for the unit ideal) and all $a_1,a_2\in\mathbb{Q}_p^\times$, the integral $$W(a_1,a_2,k)=\int_{\mathbb{Q}_p}\psi_p(x)\,\varphi\Bigl(\begin{pmatrix}0&1\\1&0\end{pmatrix}\begin{pmatrix}1&x\\0&1\end{pmatrix}\mathrm{diag}(a_1,a_2)\,k\Bigr)\,dx,$$ taken against the self-dual Haar measure `selfDualHaarAt ℚ p` and with $\psi_p$ the local component `psiLocal` of the standard adelic additive character, satisfies $\|W(a_1,a_2,k)\| \le C\,\|a_1\|^{\sigma_1+1/2}\,\|a_2\|^{\sigma_0-1/2}$, and moreover $W(a_1,a_2,k)=0$ whenever the valuation of $a_1a_2^{-1}$ exceeds `WithZero.exp M₁`.
--
--   This is the Iwasawa-coordinate gauge estimate for the Whittaker function obtained as the Jacquet integral of a vector in a principal series of $\mathrm{GL}_2(\mathbb{Q}_p)$, in the chamber $\sigma_1<\sigma_0$: a majorant of the expected shape in $\|a_1\|,\|a_2\|$, together with vanishing once $a_1/a_2$ is large. It supplies the local convergence input for the Rankin–Selberg integrals, being used for the integrability of the Fourier-transformed Godement-type integrand and for a global majorant for admissible data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_norm_jacquetIntegral_principalSeries2_diagUnits2_mul_le_and_eq_zero_of_chamber.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_forall_norm_jacquetIntegral_principalSeries2_diagUnits2_mul_le_and_eq_zero_of_chamber
    (p : HeightOneSpectrum (𝓞 ℚ))

    (μ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hμ : ∀ i, IsLocallyConstant (μ i))
    (σ : Fin 2 → ℝ)
    (hσ : ∀ (i : Fin 2) (a : (p.adicCompletion ℚ)ˣ), ‖((μ i a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (σ i))
    (h01 : σ 1 < σ 0)
    (φ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ : φ ∈ principalSeries2 p μ)
    :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    ∃ (C : ℝ) (M₁ : ℤ), 0 ≤ C ∧
      ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ a₁ a₂ : (p.adicCompletion ℚ)ˣ,
        ‖(∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
            φ (antidiagonal2 p * upperUnipotent2 p x * (diagUnits2 a₁ a₂ * k)) ∂(selfDualHaarAt ℚ p))‖ ≤
          C * ‖((a₁ : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))‖ ^ (σ 1 + 1 / 2) * ‖((a₂ : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))‖ ^ (σ 0 - 1 / 2) ∧
        (WithZero.exp M₁ < Valued.v ((a₁ * a₂⁻¹ : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) →
          (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
            φ (antidiagonal2 p * upperUnipotent2 p x * (diagUnits2 a₁ a₂ * k)) ∂(selfDualHaarAt ℚ p)) = 0) := by sorry
