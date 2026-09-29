-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_le_setIntegral_localLevelOne_dualJacquet_mul_partner_mul_eq_zero_of_dualTorusZeta_polynomial
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_le_setIntegral_localLevelOne_dualJacquet_mul_partner_mul_eq_zero_of_dualTorusZeta_polynomial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/f8aab5cf-a631-5e60-8124-152e6e027aa0
-- title:
--   Vanishing of deep dual torus shells over K₀
-- statement:
--   Let $p$ be a height-one prime of $\mathcal{O}_{\mathbb{Q}}$ and write $F = \mathbb{Q}_p$ for the completion `p.adicCompletion ℚ`. Given a pair $\mu = (\mu_0,\mu_1)$ of group homomorphisms $F^{\times}\to\mathbb{C}^{\times}$, each locally constant, together with real exponents $\sigma_0,\sigma_1$ satisfying $\|\mu_i(a)\| = \|a\|^{\sigma_i}$ for all $a$, and $\sigma_1<\sigma_0$; a function $\varphi:\mathrm{GL}_2(F)\to\mathbb{C}$ in `principalSeries2 p μ`, i.e. locally constant, left invariant under the upper unipotents $\binom{1\ x}{0\ 1}$, and satisfying $\varphi(\mathrm{diag}(a)g)=\mathrm{torusChar2}(a)\,\mathrm{halfModulus2}(a)\,\varphi(g)$; a character $\theta_0$ of $F^{\times}$ and a function $w_2:\mathrm{GL}_2(F)\to\mathbb{C}$ with $w_2(\binom{1\ x}{0\ 1}g)=\psi_p(x)w_2(g)$ for the standard local additive character $\psi_p$, right invariant under some open subgroup, and with central behaviour $w_2(z\cdot g)=\theta_0(z)w_2(g)$ for scalars $z$; the elements $w_J=\binom{0\ \ 1}{-1\ 0}$ and $w_0=\binom{0\ 1}{1\ 0}$ of $\mathrm{GL}_2(F)$; and a uniformiser $\varpi$, i.e. an element of the valuation ring with nonzero image and $v(\varpi)=\exp(-1)$. Assume further (`hdualZeta`) that for each $i\in\{0,1\}$ and each $h\in\mathrm{GL}_2(F)$ there are a polynomial $P_d\in\mathbb{C}[T]$, an integer $m_d$ and a real $\sigma_1'$ such that for every $s$ with $\operatorname{Re} s<\sigma_1'$ the function $y\mapsto w_2(\mathrm{diag}(y,1)w_Jh)\,\mu_i(y)^{-1}\theta_0(y)^{-1}\,|y|^{1/2-s}$ is integrable for the multiplicative Haar measure obtained by pulling back `mulMeasure (selfDualHaarAt ℚ p)` along $F^\times\hookrightarrow F$, with integral equal to $N(p)^{m_d s}\,P_d(N(p)^{-s})$, where $N(p)$ is the absolute norm of $p$. Then, for every Haar measure $\mu_2$ on $\mathrm{GL}_2(F)$ (with its Borel structure), there exists $n_{\mathrm{up}}\in\mathbb{Z}$ such that for all $n_1\ge n_{\mathrm{up}}$ and every measurable bounded $G:\mathrm{GL}_2(F)\to\mathbb{C}$ satisfying $G(\mathrm{diag}(u,1)k)=G(k)$ for all units $u$ with $v(u)=1$, one has $$\int_{K}\Bigl(\int_F \psi_p(x)\,\varphi\bigl(w_0\,\tfrac{}{}\!\binom{1\ x}{0\ 1}\!\cdot g_{n_1,k}\bigr)\,dx\Bigr)\;w_2(g_{n_1,k})\;G(k)\,d\mu_2(k)=0,$$ where $g_{n_1,k}=w_0\cdot{}^{t}\!\bigl(\mathrm{diag}(\varpi^{n_1},1)k\bigr)^{-1}$, the inner integral is against `selfDualHaarAt ℚ p` and uses the antidiagonal element `antidiagonal2 p` in place of the first factor, and $K$ is the subgroup [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤`](def/AdelicDock_LocalEmbedding.html#L178), the pullback under the local embedding $\mathrm{GL}_2(F)\to\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}}^{\mathrm{fin}})$ of the finite-adelic level-one subgroup for the unit ideal.
--
--   This is the statement that the deep torus shells in the shellwise expansion of the dual local $\mathrm{GL}(2)\times\mathrm{GL}(2)$ Rankin–Selberg integral contribute nothing: once the torus parameter $\varpi^{n_1}$ is pushed far enough, the shell integral over the level-one subgroup vanishes identically against any bounded weight invariant under the unit torus. It is used in the computation of the dual $(2,2)$ local Rankin–Selberg integral as a Laurent polynomial in $N(p)^{-s}$, via [`LanglandsTunnell.RankinSelberg.exists_rsLocalIntegral22_dual_mul_one_sub_eq_cpow_mul_eval_of_principalSeries2_of_forall_torusZeta_polynomial`](thm.html#LanglandsTunnell.RankinSelberg.exists_rsLocalIntegral22_dual_mul_one_sub_eq_cpow_mul_eval_of_principalSeries2_of_forall_torusZeta_polynomial).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_le_setIntegral_localLevelOne_dualJacquet_mul_partner_mul_eq_zero_of_dualTorusZeta_polynomial.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_forall_le_setIntegral_localLevelOne_dualJacquet_mul_partner_mul_eq_zero_of_dualTorusZeta_polynomial
    (p : HeightOneSpectrum (𝓞 ℚ))
    (μ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hμ : ∀ i, IsLocallyConstant (μ i))
    (σ : Fin 2 → ℝ) (hσ : ∀ (i : Fin 2) (a : (p.adicCompletion ℚ)ˣ), ‖((μ i a : ℂˣ) : ℂ)‖ = ‖(a : (p.adicCompletion ℚ))‖ ^ (σ i))
    (h01 : σ 1 < σ 0)
    (φ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ : φ ∈ principalSeries2 p μ)
    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (w₂ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)), w₂ (UnramifiedWhittaker.unipotent x * g) =
      NumberField.StandardAddChar.psiLocal ℚ p x * w₂ g)
    (hw₂sm : ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂ (g * k) = w₂ g)
    (hw₂cen : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)), w₂ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂ g)
    (wJ : GL (Fin 2) (p.adicCompletion ℚ)) (hwJ : (wJ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; -1, 0])

    (hdualZeta : letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
      ∀ (i : Fin 2) (h : GL (Fin 2) (p.adicCompletion ℚ)), ∃ (Pd : Polynomial ℂ) (md : ℤ) (σ₁ : ℝ), ∀ s : ℂ, s.re < σ₁ →
      Integrable (fun y : (p.adicCompletion ℚ)ˣ => w₂ (diagOne y * wJ * h) * (((μ i y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
          ((modulus (y : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (1 / 2 - s)) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
      ∫ y : (p.adicCompletion ℚ)ˣ, w₂ (diagOne y * wJ * h) * (((μ i y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
          ((modulus (y : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (1 / 2 - s) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) =
        (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
    ∃ nup : ℤ, ∀ n₁ : ℤ, nup ≤ n₁ →
      ∀ (Gw : GL (Fin 2) (p.adicCompletion ℚ) → ℂ), Measurable Gw → (∃ B : ℝ, ∀ k, ‖Gw k‖ ≤ B) →
        (∀ (u : (p.adicCompletion ℚ)ˣ), Valued.v (u : (p.adicCompletion ℚ)) = 1 → ∀ k : GL (Fin 2) (p.adicCompletion ℚ), Gw (diagOne u * k) = Gw k) →
        ∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
            (∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                φ (antidiagonal2 p * upperUnipotent2 p x * (w₀p * transposeInvN (Fin 2)
                  (diagOne ((Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) ^ n₁) * k)))
                ∂(selfDualHaarAt ℚ p)) *
              w₂ (w₀p * transposeInvN (Fin 2)
                (diagOne ((Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) ^ n₁) * k)) * Gw k ∂μ₂ = 0 := by sorry
