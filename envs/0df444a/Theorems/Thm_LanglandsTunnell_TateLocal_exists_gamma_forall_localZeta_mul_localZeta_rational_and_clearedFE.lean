-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_exists_gamma_forall_localZeta_mul_localZeta_rational_and_clearedFE
-- name    : LanglandsTunnell.TateLocal.exists_gamma_forall_localZeta_mul_localZeta_rational_and_clearedFE
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/c8888e8d-3110-598b-a337-e247bf491d08
-- title:
--   Product of two local Tate zeta integrals: rationality and cleared functional equation
-- statement:
--   Let $p$ be a nonzero prime ideal of $\mathbb{Z}=\mathcal{O}_{\mathbb{Q}}$, write $F=\mathbb{Q}_p$ for the $p$-adic completion and $q=\operatorname{absNorm}(p)$, and let $\mu,\nu\colon F^{\times}\to\mathbb{C}^{\times}$ be group homomorphisms that are locally constant. Then there are polynomials $\Gamma_n,\Gamma_d\in\mathbb{C}[X]$, both nonzero, and an integer $e_\Gamma$, depending only on $p,\mu,\nu$, with the following property. For every pair of functions $\varphi_1,\varphi_2\colon F\to\mathbb{C}$ that are locally constant with compact support there are polynomials $P,P_d,Q,Q_d$ with $Q,Q_d\neq 0$, integers $m,m_d$ and reals $\sigma,\sigma_d$ such that: (i) for $\operatorname{Re} s>\sigma$ the functions $a\mapsto \varphi_1(a)\mu(a)|a|^{s}$ and $d\mapsto \varphi_2(d)\nu(d)|d|^{s}$ are integrable on $F^{\times}$ for the measure obtained by restricting the self-dual Haar measure $dx$ at $p$ to $F\setminus\{0\}$, weighting by $|x|^{-1}$ and pulling back along $F^{\times}\hookrightarrow F$, and the product of their integrals, multiplied by $Q(q^{-s})$, equals $q^{ms}P(q^{-s})$; here $|x|$ denotes the modulus $\operatorname{distribHaarChar}$ of multiplication by $x$; (ii) the same holds for $\operatorname{Re} s>\sigma_d$ with $\varphi_i$ replaced by its Tate–Fourier transform $y\mapsto\int \varphi_i(x)\psi_p(xy)\,dx$ for the standard local additive character $\psi_p$, with $\mu,\nu$ replaced by $\mu^{-1},\nu^{-1}$ and the exponent $s$ by $1+s$, yielding $q^{m_d s}P_d(q^{-s})$ after clearing by $Q_d(q^{-s})$; and (iii) for every $s\in\mathbb{C}$,
--   $$q^{m_d s}P_d(q^{-s})\,Q(q^{s})\,\Gamma_d(q^{-s})=\Gamma_n(q^{-s})\,q^{e_\Gamma s}\,q^{-ms}P(q^{s})\,Q_d(q^{-s}).$$
--
--   This is the two-variable ($\mathrm{GL}_1\times\mathrm{GL}_1$) form of Tate's local theory: rationality in $q^{-s}$ of the zeta integrals of a product test function, together with the local functional equation in cleared form, the $\gamma$-factor data $(\Gamma_n,\Gamma_d,e_\Gamma)$ being independent of the test functions. It feeds the construction of the local factors at finite places for representations induced from characters, and is used by the corresponding statement for two-variable zeta integrals of general (not necessarily product) test functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_exists_gamma_forall_localZeta_mul_localZeta_rational_and_clearedFE.lean

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

theorem LanglandsTunnell.TateLocal.exists_gamma_forall_localZeta_mul_localZeta_rational_and_clearedFE
    (p : HeightOneSpectrum (𝓞 ℚ))
    (μ ν : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hμ : IsLocallyConstant μ) (hν : IsLocallyConstant ν) :
    letI := localBorel ℚ p
    ∃ (Γn Γd : Polynomial ℂ) (eΓ : ℤ), Γn ≠ 0 ∧ Γd ≠ 0 ∧
      ∀ (φ₁ φ₂ : p.adicCompletion ℚ → ℂ), IsSchwartzBruhat φ₁ → IsSchwartzBruhat φ₂ →
        ∃ (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (σ σd : ℝ), Q ≠ 0 ∧ Qd ≠ 0 ∧

          (∀ s : ℂ, σ < s.re →
            Integrable (fun a : (p.adicCompletion ℚ)ˣ =>
              φ₁ (a : p.adicCompletion ℚ) * ((μ a : ℂˣ) : ℂ) * ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s)
              (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
            Integrable (fun d : (p.adicCompletion ℚ)ˣ =>
              φ₂ (d : p.adicCompletion ℚ) * ((ν d : ℂˣ) : ℂ) * ((modulus (d : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s)
              (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
            (∫ a : (p.adicCompletion ℚ)ˣ,
                φ₁ (a : p.adicCompletion ℚ) * ((μ a : ℂˣ) : ℂ) * ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s
                ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) *
              (∫ d : (p.adicCompletion ℚ)ˣ,
                φ₂ (d : p.adicCompletion ℚ) * ((ν d : ℂˣ) : ℂ) * ((modulus (d : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s
                ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) * Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧

          (∀ s : ℂ, σd < s.re →
            Integrable (fun a : (p.adicCompletion ℚ)ˣ =>
              tateFourier (NumberField.StandardAddChar.psiLocal ℚ p) (selfDualHaarAt ℚ p) φ₁ (a : p.adicCompletion ℚ) *
                ((μ⁻¹ a : ℂˣ) : ℂ) * ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 + s))
              (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
            Integrable (fun d : (p.adicCompletion ℚ)ˣ =>
              tateFourier (NumberField.StandardAddChar.psiLocal ℚ p) (selfDualHaarAt ℚ p) φ₂ (d : p.adicCompletion ℚ) *
                ((ν⁻¹ d : ℂˣ) : ℂ) * ((modulus (d : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 + s))
              (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
            (∫ a : (p.adicCompletion ℚ)ˣ,
                tateFourier (NumberField.StandardAddChar.psiLocal ℚ p) (selfDualHaarAt ℚ p) φ₁ (a : p.adicCompletion ℚ) *
                  ((μ⁻¹ a : ℂˣ) : ℂ) * ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 + s)
                ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) *
              (∫ d : (p.adicCompletion ℚ)ˣ,
                tateFourier (NumberField.StandardAddChar.psiLocal ℚ p) (selfDualHaarAt ℚ p) φ₂ (d : p.adicCompletion ℚ) *
                  ((ν⁻¹ d : ℂˣ) : ℂ) * ((modulus (d : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 + s)
                ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) * Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧

          (∀ s : ℂ,
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) *
                Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) * Γd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              Γn.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((eΓ : ℂ) * s) *
                ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s)) *
                Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) := by sorry
