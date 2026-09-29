-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_rational_forall_torusZeta_fe_twist_of_irreducible_admissible
-- name    : LanglandsTunnell.RankinSelberg.exists_rational_forall_torusZeta_fe_twist_of_irreducible_admissible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/f38c62f1-cd7a-565e-ac59-8ad2c3f915b3
-- title:
--   Local functional equation with vector-independent γ-factor
-- statement:
--   Fix a height-one prime $p$ of $\mathcal O_{\mathbb Q}$, a homomorphism $\theta_0\colon (\mathbb Q_p)^\times\to\mathbb C^\times$ (writing $\mathbb Q_p$ for `p.adicCompletion ℚ`), a nonzero ideal $N$, and a function $w_2\colon \mathrm{GL}_2(\mathbb Q_p)\to\mathbb C$ such that $w_2(u(x)g)=\psi_p(x)\,w_2(g)$ for the standard local additive character $\psi_p$ and all unipotent $u(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$, $w_2$ is right invariant under [`AdelicDock.localLevelOne`](def/AdelicDock_LocalEmbedding.html#L178), the pullback to $\mathrm{GL}_2(\mathbb Q_p)$ of the adelic level-one subgroup of level $N$, $w_2\neq 0$, every nonzero $w$ in the span $V$ of the right translates of $w_2$ has $w_2$ in the span of its own right translates, for each open subgroup $U$ some finite set of functions spans all $U$-right-invariant vectors of $V$, and $w_2(zg)=\theta_0(z)w_2(g)$ for scalar matrices $z$. Let $w_J$ have matrix $\begin{pmatrix}0&1\\-1&0\end{pmatrix}$ and $\eta\colon(\mathbb Q_p)^\times\to\mathbb C^\times$ be locally constant. Then, with the Borel structure on $\mathbb Q_p$, there are nonzero $\Gamma^n,\Gamma^d\in\mathbb C[X]$ and $a\in\mathbb Z$ such that for every $w\in V$ there are $P,Q,P^d,Q^d$ with $Q,Q^d\neq0$, integers $m,m^d$ and reals $\sigma_0,\sigma_1$ with: for $\mathrm{Re}\,s>\sigma_0$ the function $y\mapsto w(\mathrm{diag}(y,1))\eta(y)|y|^{s-1/2}$ is integrable for the multiplicative Haar measure on $(\mathbb Q_p)^\times$ obtained from the self-dual additive measure, and its integral times $Q(q^{-s})$ equals $q^{ms}P(q^{-s})$, where $q=\mathrm{absNorm}(p)$ and $|\cdot|$ is the modulus; for $\mathrm{Re}\,s<\sigma_1$ the function $y\mapsto w(\mathrm{diag}(y,1)w_J)\eta(y)^{-1}\theta_0(y)^{-1}|y|^{1/2-s}$ is likewise integrable with integral times $Q^d(q^{-s})$ equal to $q^{m^ds}P^d(q^{-s})$; and for all $s\in\mathbb C$, $\Gamma^d(q^{-s})\,q^{m^ds}P^d(q^{-s})\,Q(q^{-s})=\Gamma^n(q^{-s})\,q^{as}\,q^{ms}P(q^{-s})\,Q^d(q^{-s})$.
--
--   This is the existence half of the local functional equation of Jacquet–Langlands for an irreducible admissible generic representation of $\mathrm{GL}_2(\mathbb Q_p)$ in its $\psi_p$-Whittaker model, twisted by a locally constant quasi-character $\eta$: the $\gamma$-factor, presented cleared of denominators as a rational function of $q^{-s}$, is one and the same for all vectors of the representation. It feeds the global Rankin–Selberg comparison of zeta integrals used in the converse-theorem input to the Langlands–Tunnell theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_rational_forall_torusZeta_fe_twist_of_irreducible_admissible.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_rational_forall_torusZeta_fe_twist_of_irreducible_admissible
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

    (η : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hη : IsLocallyConstant η) :
    letI := localBorel ℚ p

    ∃ (Γn Γd : Polynomial ℂ) (a : ℤ), Γn ≠ 0 ∧ Γd ≠ 0 ∧
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∃ (P Q Pd Qd : Polynomial ℂ) (m md : ℤ) (σ₀ σ₁ : ℝ), Q ≠ 0 ∧ Qd ≠ 0 ∧
          (∀ s : ℂ, σ₀ < s.re →
            Integrable (fun y : (p.adicCompletion ℚ)ˣ => w (diagOne y) * ((η y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
          (∀ s : ℂ, σ₀ < s.re →
            (∫ y : (p.adicCompletion ℚ)ˣ, w (diagOne y) * ((η y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) * Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
          (∀ s : ℂ, s.re < σ₁ →
            Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
              w (diagOne y * wJ) * (((η y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
          (∀ s : ℂ, s.re < σ₁ →
            (∫ y : (p.adicCompletion ℚ)ˣ,
                w (diagOne y * wJ) * (((η y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) * Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧

          (∀ s : ℂ,
            Γd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * ((Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) * Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              Γn.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((a : ℂ) * s) *
                ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) * Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) := by sorry
