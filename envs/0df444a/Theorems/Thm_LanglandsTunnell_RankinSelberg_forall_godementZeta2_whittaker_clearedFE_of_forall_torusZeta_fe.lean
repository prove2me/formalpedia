-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe
-- name    : LanglandsTunnell.RankinSelberg.forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/07ea0dc4-0982-51eb-b818-88c19d1bd1a4
-- title:
--   Cleared local Godement–Jacquet functional equation for Whittaker coefficients
-- statement:
--   Fix a finite place $p$ of $\mathbb{Q}$, write $F_p$ for the completion, $q=\mathrm{absNorm}(p)$, and let $\psi_p$ be the standard local additive character. The data are: a character $\theta_0\colon F_p^{\times}\to\mathbb{C}^{\times}$; a nonzero ideal $N$ of $\mathcal{O}_{\mathbb{Q}}$; a function $w_{2}^{\mathrm{base}}\colon \mathrm{GL}_2(F_p)\to\mathbb{C}$ subject to the hypotheses, summarised here, that it transforms by $\psi_p(x)$ under left translation by the upper unipotent $\begin{pmatrix}1&x\\0&1\end{pmatrix}$, is right invariant under the subgroup obtained by pulling back the finite-adelic level-one subgroup of $N$ along the embedding of $\mathrm{GL}_2(F_p)$ into the finite adelic points, is nonzero, is recovered from the right-translation span of any nonzero member of its own right-translation span (irreducibility), has the right-$U$-invariant part of that span finitely spanned for every open subgroup $U$ (admissibility), and satisfies $w_{2}^{\mathrm{base}}(zg)=\theta_0(z)w_{2}^{\mathrm{base}}(g)$ for scalar $z$; an element $w_J$ of $\mathrm{GL}_2(F_p)$ with matrix $\begin{pmatrix}0&1\\-1&0\end{pmatrix}$; a locally constant character $\chi$ of $F_p^{\times}$; and $E_0\in\mathbb{C}$, $e_0\in\mathbb{Z}$. The hypothesis `hfe` requires of every $w$ in the right-translation span of $w_{2}^{\mathrm{base}}$ polynomials $P,P_d$, integers $m,m_d$ and reals $\sigma_0,\sigma_1$ such that, against the multiplicative measure built from the self-dual additive Haar measure of $F_p$, the integral of $w(\mathrm{diag}(y,1))\chi(y)|y|^{s-1/2}$ converges for $\mathrm{Re}\,s>\sigma_0$ with value $q^{ms}P(q^{-s})$, the integral of $w(\mathrm{diag}(y,1)w_J)\chi(y)^{-1}\theta_0(y)^{-1}|y|^{1/2-s}$ converges for $\mathrm{Re}\,s<\sigma_1$ with value $q^{m_ds}P_d(q^{-s})$, and $q^{m_ds}P_d(q^{-s})=E_0q^{e_0s}\,q^{ms}P(q^{-s})$ identically. The conclusion asserts, for every Haar measure $\mu_2$ on $\mathrm{GL}_2(F_p)$ (for the Borel structure), every $w$ in the span, every locally constant compactly supported $\Phi$ on $M_2(F_p)$, all polynomials $P,P_d,Q,Q_d$ with $Q\neq0$, $Q_d\neq0$, all integers $m,m_d$ and reals $\sigma_2,\sigma_3$: if the Godement–Jacquet integrand $w(g)\Phi(g)\chi(\det g)|\det g|^{s+1/2}$ is $\mu_2$-integrable for $\mathrm{Re}\,s>\sigma_2$ with $\mathrm{godementZeta2}$ at $s+1/2$ satisfying $Z(s+1/2)Q(q^{-s})=q^{ms}P(q^{-s})$ there, and the dual integrand built from $g\mapsto w({}^{t}g^{-1})$, the two-step column Fourier transform `matFourier22` of $\Phi$ with respect to $\psi_p$, $\chi^{-1}$ and $|\det g|^{s+3/2}$ is integrable for $\mathrm{Re}\,s>\sigma_3$ with $Z^{\vee}(s+3/2)Q_d(q^{-s})=q^{m_ds}P_d(q^{-s})$ there, then for all $s\in\mathbb{C}$ the cleared identity $$q^{m_ds}P_d(q^{-s})\,Q(q^{s})=E_0\,q^{-e_0s}\,q^{-ms}P(q^{s})\,Q_d(q^{-s})$$ holds, the constant factors being written as evaluations of the polynomials $1$ and $C(E_0)$ at $q^{s}$.
--
--   This is the local Godement–Jacquet functional equation for $\mathrm{GL}_2$ over a $p$-adic field, in the form of an identity between the rational expressions that represent the zeta integral of a Whittaker vector and that of its Fourier-dual, with the $\gamma$-factor $E_0q^{e_0s}$ imported from the $\mathrm{GL}_2\times\mathrm{GL}_1$ torus zeta functional equation. It is obtained by splitting according to whether the Kirillov model vanishes near zero or a Borel eigenfunctional exists, and it feeds the converse-theorem input used in the Rankin–Selberg stage.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe.lean

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

theorem LanglandsTunnell.RankinSelberg.forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe
    (p : HeightOneSpectrum (𝓞 ℚ))

    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      w ≠ 0 → w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))
    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    (wJ : GL (Fin 2) (p.adicCompletion ℚ)) (hwJ : (wJ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; -1, 0])

    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)

    (E₀ : ℂ) (e₀ : ℤ)
    (hfe : letI := localBorel ℚ p
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₀ σ₁ : ℝ),
        (∀ s : ℂ, σ₀ < s.re →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, σ₀ < s.re →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y * wJ) * (((χ y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
              ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y * wJ) * (((χ y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ,
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            (E₀ * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e₀ : ℂ) * s)) *
              ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))))
    :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∀ (Φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ), IsLocallyConstant Φ → HasCompactSupport Φ →
          ∀ (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ), Q ≠ 0 → Qd ≠ 0 →

            (∀ s : ℂ, σ₂ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                w g * Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2)) μ₂) →

            (∀ s : ℂ, σ₂ < s.re →
              godementZeta2 p μ₂ w Φ χ (s + 1 / 2) * Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) →

            (∀ s : ℂ, σ₃ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                w (transposeInvN (Fin 2) g) *
                  matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
                  ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 3 / 2)) μ₂) →

            (∀ s : ℂ, σ₃ < s.re →
              godementZeta2 p μ₂ (fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (transposeInvN (Fin 2) g))
                  (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ) χ⁻¹ (s + 3 / 2) * Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) →

            (∀ s : ℂ,
              ((1 : Polynomial ℂ)).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) *
                  ((Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) *
                  Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) =
                ((Polynomial.C E₀).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) * (Ideal.absNorm p.asIdeal : ℂ) ^ (((-e₀ : ℤ) : ℂ) * s)) *
                  ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s)) *
                  Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) := by sorry
