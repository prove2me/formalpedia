-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_exists_gamma_forall_localZeta_rational_and_clearedFE
-- name    : LanglandsTunnell.TateLocal.exists_gamma_forall_localZeta_rational_and_clearedFE
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/7514436e-fe9e-500d-94ab-b83cbe826d4b
-- title:
--   Rational local Tate zeta integrals and cleared functional equation
-- statement:
--   Fix a nonzero prime $\mathfrak p$ of the ring of integers of $\mathbb Q$, write $F=\mathbb Q_{\mathfrak p}$ for the completion, $q=N\mathfrak p$ for the absolute norm of $\mathfrak p$, and equip $F$ with its Borel $\sigma$-algebra; let $\mu\colon F^{\times}\to\mathbb C^{\times}$ be a group homomorphism that is locally constant. Then there are polynomials $\Gamma_n,\Gamma_d\in\mathbb C[X]$, both nonzero, and an integer $e_\Gamma$, depending only on $\mathfrak p$ and $\mu$, with the following property. For every $\varphi\colon F\to\mathbb C$ that is Schwartz–Bruhat, i.e. locally constant with compact support, there are polynomials $P,P_d,Q,Q_d$ with $Q\neq 0$, $Q_d\neq 0$, integers $m,m_d$ and reals $\sigma,\sigma_d$ such that three assertions hold. First, for every $s$ with $\operatorname{Re}s>\sigma$ the function $a\mapsto \varphi(a)\mu(a)|a|^{s}$ on $F^{\times}$ is integrable for the multiplicative measure obtained by pulling back along $a\mapsto a$ the measure $|x|^{-1}\,dx$ on $F\setminus\{0\}$, where $dx$ is the self-dual Haar measure `selfDualHaarAt` (additive Haar measure giving the integers mass one, scaled by $q^{-\mathrm{level}(\psi)/2}$) and $|x|$ is the module `modulus` (the scaling factor of $dx$ under multiplication by $x$), and $$\Big(\int_{F^{\times}}\varphi(a)\mu(a)|a|^{s}\,d^{\times}a\Big)\,Q(q^{-s})=q^{ms}P(q^{-s}).$$ Second, the same statement with $\varphi$ replaced by its Tate–Fourier transform $\hat\varphi(y)=\int_F\varphi(x)\psi(xy)\,dx$ for the local component $\psi$ of the standard adelic additive character, with $\mu$ replaced by $\mu^{-1}$ and $|a|^{s}$ by $|a|^{1+s}$: for $\operatorname{Re}s>\sigma_d$ the integrand is integrable and the integral times $Q_d(q^{-s})$ equals $q^{m_ds}P_d(q^{-s})$. Third, for all $s\in\mathbb C$ the polynomial identity $$q^{m_ds}P_d(q^{-s})\,Q(q^{s})\,\Gamma_d(q^{-s})=\Gamma_n(q^{-s})\,q^{e_\Gamma s}\,\big(q^{-ms}P(q^{s})\big)\,Q_d(q^{-s})$$ holds, with no restriction on $s$.
--
--   This is Tate's local theory at a finite place of $\mathbb Q$, packaged as rationality of the zeta integral in $q^{-s}$ together with a denominator-cleared local functional equation whose $\gamma$-factor data $(\Gamma_n,\Gamma_d,e_\Gamma)$ is uniform in the test function; informally $Z(\hat\varphi,\mu^{-1},1+s)=\gamma\,Z(\varphi,\mu,-s)$ as rational functions. It feeds the corresponding two-variable statement [`LanglandsTunnell.TateLocal.exists_gamma_forall_localZeta_mul_localZeta_rational_and_clearedFE`](thm.html#LanglandsTunnell.TateLocal.exists_gamma_forall_localZeta_mul_localZeta_rational_and_clearedFE) used in the Rankin–Selberg and converse-theorem part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_exists_gamma_forall_localZeta_rational_and_clearedFE.lean

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
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection

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

theorem LanglandsTunnell.TateLocal.exists_gamma_forall_localZeta_rational_and_clearedFE
    (p : HeightOneSpectrum (𝓞 ℚ))
    (μ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hμ : IsLocallyConstant μ) :
    letI := localBorel ℚ p
    ∃ (Γn Γd : Polynomial ℂ) (eΓ : ℤ), Γn ≠ 0 ∧ Γd ≠ 0 ∧
      ∀ (φ : p.adicCompletion ℚ → ℂ), IsSchwartzBruhat φ →
        ∃ (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (σ σd : ℝ), Q ≠ 0 ∧ Qd ≠ 0 ∧

          (∀ s : ℂ, σ < s.re →
            Integrable (fun a : (p.adicCompletion ℚ)ˣ =>
              φ (a : p.adicCompletion ℚ) * ((μ a : ℂˣ) : ℂ) * ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s)
              (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
            (∫ a : (p.adicCompletion ℚ)ˣ,
                φ (a : p.adicCompletion ℚ) * ((μ a : ℂˣ) : ℂ) * ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s
                ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) * Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧

          (∀ s : ℂ, σd < s.re →
            Integrable (fun a : (p.adicCompletion ℚ)ˣ =>
              tateFourier (NumberField.StandardAddChar.psiLocal ℚ p) (selfDualHaarAt ℚ p) φ (a : p.adicCompletion ℚ) *
                ((μ⁻¹ a : ℂˣ) : ℂ) * ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 + s))
              (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
            (∫ a : (p.adicCompletion ℚ)ˣ,
                tateFourier (NumberField.StandardAddChar.psiLocal ℚ p) (selfDualHaarAt ℚ p) φ (a : p.adicCompletion ℚ) *
                  ((μ⁻¹ a : ℂˣ) : ℂ) * ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 + s)
                ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) * Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧

          (∀ s : ℂ,
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) *
                Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) * Γd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              Γn.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((eΓ : ℂ) * s) *
                ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s)) *
                Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) := by sorry
