-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_gamma_forall_rational_godementZeta2_principalSeries2_and_clearedFE
-- name    : LanglandsTunnell.RankinSelberg.exists_gamma_forall_rational_godementZeta2_principalSeries2_and_clearedFE
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/1420b10a-e128-5348-9b86-0d77e5ad4956
-- title:
--   Rationality and cleared functional equation for local GL₂ zeta integrals
-- statement:
--   Let $p$ be a height-one prime of $\mathcal{O}_{\mathbb Q}$, write $F=\mathbb Q_p$ for the completion $p.adicCompletion\ \mathbb Q$ and $q=$ `Ideal.absNorm p.asIdeal`, and let $\lambda_0,\lambda_1$ and $\chi$ be locally constant homomorphisms $F^\times\to\mathbb C^\times$. With the Borel $\sigma$-algebras on $F$ and on $GL_2(F)$ furnished by `localBorel` and `localGLBorel`, the assertion is that there exist nonzero $\Gamma_n,\Gamma_d\in\mathbb C[X]$ and $e_\Gamma\in\mathbb Z$, depending only on $\lambda$ and $\chi$, such that for every Haar measure $\mu_2$ on $GL_2(F)$, every $F_\lambda$ in the submodule `principalSeries2 p lam` (locally constant functions on $GL_2(F)$, invariant under left translation by the upper unipotents $\begin{pmatrix}1&x\\0&1\end{pmatrix}$, and satisfying $F_\lambda(\mathrm{diag}(a_0,a_1)g)=\lambda_0(a_0)\lambda_1(a_1)\sqrt{\|a_0\|/\|a_1\|}\,F_\lambda(g)$), and every locally constant compactly supported $\Phi:M_2(F)\to\mathbb C$, there are $P,P_d,Q,Q_d\in\mathbb C[X]$ with $Q,Q_d\neq0$, integers $m,m_d$ and reals $\sigma_2,\sigma_3$ such that: for $\mathrm{Re}\,s>\sigma_2$ the function $g\mapsto F_\lambda(g)\Phi(g)\chi(\det g)\,\mathrm{modulus}(\det g)^{s+1/2}$ is $\mu_2$-integrable and `godementZeta2` at $s+\tfrac12$ satisfies $Z(s+\tfrac12)Q(q^{-s})=q^{ms}P(q^{-s})$; for $\mathrm{Re}\,s>\sigma_3$ the same holds for the dual integrand $g\mapsto F_\lambda({}^t g^{-1})\,\widehat\Phi(g)\,\chi^{-1}(\det g)\,\mathrm{modulus}(\det g)^{s+3/2}$, with $\widehat\Phi=$ `matFourier22` the iterated column-wise Fourier transform of $\Phi$ against the standard local additive character `psiLocal`, giving $Z^\vee(s+\tfrac32)Q_d(q^{-s})=q^{m_ds}P_d(q^{-s})$; and for all $s\in\mathbb C$ the cleared identity $q^{m_ds}P_d(q^{-s})Q(q^{s})\Gamma_d(q^{-s})=\Gamma_n(q^{-s})q^{e_\Gamma s}\bigl(q^{-ms}P(q^{s})\bigr)Q_d(q^{-s})$ holds.
--
--   This is the local Godement–Jacquet theory at a finite place for sections of the normalised principal series of $GL_2$ rather than for matrix coefficients: absolute convergence in a right half-plane, rationality of the zeta integral in $q^{-s}$, and a functional equation relating the integral of $(F_\lambda,\Phi)$ to that of $({}^tg^{-1},\widehat\Phi)$ through a $\gamma$-factor $\Gamma_n/\Gamma_d$ together with the shift $q^{e_\Gamma s}$, the $\gamma$-factor being independent of the Haar measure, of the section and of the test function. It feeds the Whittaker-side functional equation used in the converse-theorem input, via [`LanglandsTunnell.RankinSelberg.forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_borelEigenfunctional`](thm.html#LanglandsTunnell.RankinSelberg.forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_borelEigenfunctional).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_gamma_forall_rational_godementZeta2_principalSeries2_and_clearedFE.lean

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
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2

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

theorem LanglandsTunnell.RankinSelberg.exists_gamma_forall_rational_godementZeta2_principalSeries2_and_clearedFE
    (p : HeightOneSpectrum (𝓞 ℚ))
    (lam : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i))
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∃ (Γn Γd : Polynomial ℂ) (eΓ : ℤ), Γn ≠ 0 ∧ Γd ≠ 0 ∧
      ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
      ∀ F ∈ principalSeries2 p lam,
      ∀ (Φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ), IsLocallyConstant Φ → HasCompactSupport Φ →
        ∃ (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ), Q ≠ 0 ∧ Qd ≠ 0 ∧

          (∀ s : ℂ, σ₂ < s.re →
            Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              F g * Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2)) μ₂) ∧

          (∀ s : ℂ, σ₂ < s.re →
            godementZeta2 p μ₂ F Φ χ (s + 1 / 2) * Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧

          (∀ s : ℂ, σ₃ < s.re →
            Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              F (transposeInvN (Fin 2) g) *
                matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
                ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 3 / 2)) μ₂) ∧

          (∀ s : ℂ, σ₃ < s.re →
            godementZeta2 p μ₂ (fun g : GL (Fin 2) (p.adicCompletion ℚ) => F (transposeInvN (Fin 2) g))
                (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ) χ⁻¹ (s + 3 / 2) *
                Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧

          (∀ s : ℂ,
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) *
                Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) * Γd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              Γn.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((eΓ : ℂ) * s) *
                ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s)) *
                Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) := by sorry
