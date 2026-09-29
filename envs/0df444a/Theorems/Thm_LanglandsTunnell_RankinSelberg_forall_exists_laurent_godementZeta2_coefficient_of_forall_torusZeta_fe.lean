-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_exists_laurent_godementZeta2_coefficient_of_forall_torusZeta_fe
-- name    : LanglandsTunnell.RankinSelberg.forall_exists_laurent_godementZeta2_coefficient_of_forall_torusZeta_fe
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/ec7e2bfb-d4d3-5205-a981-974150f9d87e
-- title:
--   Godement–Jacquet zeta integrals of GL₂ matrix coefficients
-- statement:
--   Fix a finite place $p$ of $\mathbb{Q}$, a character $\theta_0:(\mathbb{Q}_p)^\times\to\mathbb{C}^\times$, a nonzero ideal $N\subseteq\mathcal{O}_{\mathbb Q}$, and a function $w_2:\mathrm{GL}_2(\mathbb{Q}_p)\to\mathbb{C}$ subject to: the Whittaker law $w_2(\left(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\right)g)=\psi_p(x)w_2(g)$ for the standard local additive character; right invariance under the subgroup [`AdelicDock.localLevelOne`](def/AdelicDock_LocalEmbedding.html#L178) (the preimage of the finite-adelic level-one subgroup of $N$ under the local embedding); $w_2\neq 0$; an irreducibility condition (every nonzero $w$ in the span $V$ of the right translates $g\mapsto w_2(gh)$ has $w_2$ in the span of its own right translates); admissibility (for each open subgroup $U$ a finite set $B$ of functions spanning all $U$-right-invariant members of $V$); and central character $w_2(z\cdot g)=\theta_0(z)w_2(g)$ for scalar matrices. Let $wJ$ have matrix $\left(\begin{smallmatrix}0&1\\-1&0\end{smallmatrix}\right)$, let $\chi$ be a locally constant character of $(\mathbb{Q}_p)^\times$, and let $E_0\in\mathbb{C}$, $e_0\in\mathbb{Z}$. The hypothesis `hfe` requires of every $w\in V$ polynomials $P,P^\vee$, integers $m,m^\vee$ and reals $\sigma_0,\sigma_1$ such that, against the multiplicative measure obtained by comapping $\mathrm{mulMeasure}$ of the self-dual additive Haar measure along $(\mathbb{Q}_p)^\times\hookrightarrow\mathbb{Q}_p$: for $\mathrm{Re}\,s>\sigma_0$ the torus integrand $y\mapsto w(\mathrm{diag}(y,1))\chi(y)|y|^{s-1/2}$ is integrable with integral $q^{ms}P(q^{-s})$, where $q=\mathrm{N}(p)$; for $\mathrm{Re}\,s<\sigma_1$ the dual integrand $y\mapsto w(\mathrm{diag}(y,1)wJ)\chi(y)^{-1}\theta_0(y)^{-1}|y|^{1/2-s}$ is integrable with integral $q^{m^\vee s}P^\vee(q^{-s})$; and $q^{m^\vee s}P^\vee(q^{-s})=E_0q^{e_0s}\cdot q^{ms}P(q^{-s})$ for all $s$. The conclusion asserts: for every Haar measure $\mu_2$ on $\mathrm{GL}_2(\mathbb{Q}_p)$ (with the Borel structure `localGLBorel`), every $w\in V$, every $\mathbb{C}$-linear functional $\ell$ on functions $\mathrm{GL}_2(\mathbb{Q}_p)\to\mathbb{C}$ that is invariant under right translation by some open subgroup $U$ on all of $V$, and every locally constant compactly supported $\Phi$ on $M_2(\mathbb{Q}_p)$, there are polynomials $P,P^\vee$, integers $m,m^\vee$ and reals $\sigma_2,\sigma_3$ with: for $\mathrm{Re}\,s>\sigma_2$ the function $g\mapsto \ell(x\mapsto w(xg))\,\Phi(g)\,\chi(\det g)|\det g|^{s+1/2}$ is $\mu_2$-integrable and its integral, i.e. `godementZeta2` of the coefficient $c(g)=\ell(x\mapsto w(xg))$ against $\Phi$ and $\chi$ at $s+1/2$, equals $q^{ms}P(q^{-s})$; and for $\mathrm{Re}\,s>\sigma_3$ the function $g\mapsto \ell(x\mapsto w(x\,{}^{t}g^{-1}))\,\widehat{\Phi}(g)\,\chi^{-1}(\det g)|\det g|^{s+3/2}$ is $\mu_2$-integrable, $\widehat{\Phi}$ being the two-column Fourier transform `matFourier22` of $\Phi$ with respect to $\psi_p$, with `godementZeta2` of that coefficient against $\widehat\Phi$ and $\chi^{-1}$ at $s+3/2$ equal to $q^{m^\vee s}P^\vee(q^{-s})$. No functional equation linking the two Laurent polynomials is asserted, and the dual identity here holds on a right half-plane.
--
--   This is the local Godement–Jacquet rationality statement for $\mathrm{GL}_2$ in matrix-coefficient form: zeta integrals of a coefficient of the Whittaker model against a Bruhat–Schwartz function on $M_2(\mathbb{Q}_p)$ are, where convergent, Laurent polynomials in $q^{-s}$, deduced from the corresponding torus (Whittaker) functional equation hypothesis. It feeds the local analysis of Rankin–Selberg integrals, being used in [`LanglandsTunnell.RankinSelberg.exists_rsLocalIntegral_jacquetWhittaker3_mul_centralTate_eq_cpow_mul_eval_and_dual_of_chamber`](thm.html#LanglandsTunnell.RankinSelberg.exists_rsLocalIntegral_jacquetWhittaker3_mul_centralTate_eq_cpow_mul_eval_and_dual_of_chamber).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_forall_exists_laurent_godementZeta2_coefficient_of_forall_torusZeta_fe.lean

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

theorem LanglandsTunnell.RankinSelberg.forall_exists_laurent_godementZeta2_coefficient_of_forall_torusZeta_fe
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
        ∀ (ℓ : (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) →ₗ[ℂ] ℂ),
          (∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
            ∀ k ∈ U, ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
              ℓ (fun g : GL (Fin 2) (p.adicCompletion ℚ) => v (g * k)) = ℓ v) →
          ∀ (Φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ), IsLocallyConstant Φ → HasCompactSupport Φ →
            ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ),

              (∀ s : ℂ, σ₂ < s.re →
                Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ℓ (fun x : GL (Fin 2) (p.adicCompletion ℚ) => w (x * g)) * Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2)) μ₂) ∧

              (∀ s : ℂ, σ₂ < s.re →
                godementZeta2 p μ₂ (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ℓ (fun x : GL (Fin 2) (p.adicCompletion ℚ) => w (x * g))) Φ χ (s + 1 / 2) =
                  (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧

              (∀ s : ℂ, σ₃ < s.re →
                Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ℓ (fun x : GL (Fin 2) (p.adicCompletion ℚ) => w (x * transposeInvN (Fin 2) g)) *
                    matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
                    ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 3 / 2)) μ₂) ∧

              (∀ s : ℂ, σ₃ < s.re →
                godementZeta2 p μ₂ (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ℓ (fun x : GL (Fin 2) (p.adicCompletion ℚ) => w (x * transposeInvN (Fin 2) g)))
                    (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ)
                    χ⁻¹ (s + 3 / 2) =
                  (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) := by sorry
