-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_exists_laurent_godementZeta2_whittaker_of_forall_torusZeta_fe
-- name    : LanglandsTunnell.RankinSelberg.forall_exists_laurent_godementZeta2_whittaker_of_forall_torusZeta_fe
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/bb379bc0-7bd4-5ffb-aa33-9f34806a1684
-- title:
--   Laurent Godement–Jacquet integrals of GL₂ Whittaker vectors
-- statement:
--   Fix a finite place $p$ of $\mathbb{Q}$, i.e. a point of the height-one spectrum of $\mathcal{O}_{\mathbb{Q}}$, with completion $F = \mathbb{Q}_p$, residue norm $N =$ `Ideal.absNorm p.asIdeal`, and let $\theta_0 : F^{\times} \to \mathbb{C}^{\times}$ be a character. Let $N$ be a nonzero ideal of $\mathcal{O}_{\mathbb{Q}}$ and let $w_{2,\mathrm{base}} : \mathrm{GL}_2(F) \to \mathbb{C}$ satisfy: the Whittaker transformation law $w_{2,\mathrm{base}}(u(x)g) = \psi_p(x)\,w_{2,\mathrm{base}}(g)$ for the standard local additive character $\psi_p$ and the upper unipotent $u(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$; right invariance under the compact open subgroup [`AdelicDock.localLevelOne`](def/AdelicDock_LocalEmbedding.html#L178) at $p$ attached to $N$ (the pullback of the adelic level-one subgroup along the embedding at $p$); $w_{2,\mathrm{base}} \neq 0$; irreducibility of its right-translation span $V = \mathrm{span}_{\mathbb{C}}\{g \mapsto w_{2,\mathrm{base}}(gh)\}$, in the form that every nonzero $w \in V$ has $w_{2,\mathrm{base}}$ in the span of the right translates of $w$; admissibility, namely for each open subgroup $U \le \mathrm{GL}_2(F)$ a finite subset $B$ of functions whose span contains all right $U$-invariant vectors of $V$; and the central character law $w_{2,\mathrm{base}}(zI\cdot g) = \theta_0(z)w_{2,\mathrm{base}}(g)$. Let $w_J \in \mathrm{GL}_2(F)$ have matrix $\begin{pmatrix}0&1\\-1&0\end{pmatrix}$, let $\chi : F^{\times} \to \mathbb{C}^{\times}$ be locally constant, and let $E_0 \in \mathbb{C}$, $e_0 \in \mathbb{Z}$. The hypothesis `hfe` asserts that every $w \in V$ admits polynomials $P, P_d \in \mathbb{C}[X]$, integers $m, m_d$ and abscissae $\sigma_0, \sigma_1$ such that, with respect to the multiplicative measure on $F^{\times}$ obtained from the self-dual Haar measure by restricting off $0$, multiplying the density by $|\cdot|^{-1}$ and pulling back along $F^\times \hookrightarrow F$: the torus integral $\int w(\mathrm{diag}(y,1))\chi(y)|y|^{s-1/2}\,dy$ converges absolutely for $\mathrm{Re}\,s > \sigma_0$ with value $N^{ms}P(N^{-s})$; the dual torus integral $\int w(\mathrm{diag}(y,1)w_J)\chi(y)^{-1}\theta_0(y)^{-1}|y|^{1/2-s}\,dy$ converges absolutely for $\mathrm{Re}\,s < \sigma_1$ with value $N^{m_ds}P_d(N^{-s})$; and $N^{m_ds}P_d(N^{-s}) = E_0N^{e_0s}\cdot N^{ms}P(N^{-s})$ for all $s$. The conclusion: for every Haar measure $\mu_2$ on $\mathrm{GL}_2(F)$ (with its Borel structure), every $w \in V$ and every locally constant compactly supported $\Phi$ on $M_2(F)$ there are polynomials $P, P_d$, integers $m, m_d$ and reals $\sigma_2, \sigma_3$ such that $g \mapsto w(g)\Phi(g)\chi(\det g)|\det g|^{s+1/2}$ is $\mu_2$-integrable and `godementZeta2` of $(w,\Phi,\chi)$ at $s + 1/2$ equals $N^{ms}P(N^{-s})$ for $\mathrm{Re}\,s > \sigma_2$, and $g \mapsto w({}^{t}g^{-1})\,\widehat{\Phi}(g)\,\chi^{-1}(\det g)|\det g|^{s+3/2}$ is $\mu_2$-integrable and `godementZeta2` of $(g \mapsto w({}^{t}g^{-1}), \widehat{\Phi}, \chi^{-1})$ at $s + 3/2$ equals $N^{m_ds}P_d(N^{-s})$ for $\mathrm{Re}\,s > \sigma_3$, where $\widehat{\Phi} =$ `matFourier22` is the column-by-column Fourier transform of $\Phi$ with respect to $\psi_p$.
--
--   This is the local rationality statement for Godement–Jacquet zeta integrals of vectors in a Whittaker model: both the primal and the dual integral are Laurent polynomials in $N^{-s}$ with no denominators, the denominators being cleared by the assumed functional equation for the torus integrals. It feeds the extraction of Laurent coefficients and the cleared local functional equation used in the Rankin–Selberg and converse-theorem part of the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_forall_exists_laurent_godementZeta2_whittaker_of_forall_torusZeta_fe.lean

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
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
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

theorem LanglandsTunnell.RankinSelberg.forall_exists_laurent_godementZeta2_whittaker_of_forall_torusZeta_fe
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
          ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ),

            (∀ s : ℂ, σ₂ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                w g * Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2)) μ₂) ∧

            (∀ s : ℂ, σ₂ < s.re →
              godementZeta2 p μ₂ w Φ χ (s + 1 / 2) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧

            (∀ s : ℂ, σ₃ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                w (transposeInvN (Fin 2) g) *
                  matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
                  ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 3 / 2)) μ₂) ∧

            (∀ s : ℂ, σ₃ < s.re →
              godementZeta2 p μ₂ (fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (transposeInvN (Fin 2) g))
                  (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ) χ⁻¹ (s + 3 / 2) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) := by sorry
