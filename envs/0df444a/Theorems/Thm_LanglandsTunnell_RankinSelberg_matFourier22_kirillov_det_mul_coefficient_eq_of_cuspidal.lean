-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_matFourier22_kirillov_det_mul_coefficient_eq_of_cuspidal
-- name    : LanglandsTunnell.RankinSelberg.matFourier22_kirillov_det_mul_coefficient_eq_of_cuspidal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/27a30a1c-e0b4-56f1-abc7-cd9b4cfbb366
-- title:
--   Fourier transform of cuspidal Kirillov matrix-coefficient functions on M₂
-- statement:
--   Fix a finite place $p$ of $\mathbb Q$, i.e. a height-one prime of $\mathcal O_{\mathbb Q}$, write $F = \mathbb Q_p$ for the completion, let $\theta_0 : F^\times \to \mathbb C^\times$ be a group homomorphism and $N \neq 0$ an ideal of $\mathcal O_{\mathbb Q}$. Let $w_{2,\mathrm{base}} : \mathrm{GL}_2(F) \to \mathbb C$ satisfy: the Whittaker law $w_{2,\mathrm{base}}\big(\begin{pmatrix}1&x\\0&1\end{pmatrix}g\big) = \psi_p(x)\,w_{2,\mathrm{base}}(g)$ for the local standard additive character $\psi_p =$ `psiLocal`; right invariance under `localLevelOne`, the subgroup of $\mathrm{GL}_2(F)$ pulled back along the local embedding from the level-one subgroup of $\mathrm{GL}_2$ of the finite adèles attached to $N$; $w_{2,\mathrm{base}} \neq 0$; irreducibility, in the form that every nonzero element $w$ of the span $V$ of the right translates $g \mapsto w_{2,\mathrm{base}}(gh)$ has $w_{2,\mathrm{base}}$ in the span of its own right translates; admissibility, in the form that for every open subgroup $U$ there is a finite set $B$ of functions spanning all $U$-right-invariant elements of $V$; the central character condition $w_{2,\mathrm{base}}(z\cdot g) = \theta_0(z)\,w_{2,\mathrm{base}}(g)$ for scalar matrices $z \in F^\times$; and cuspidality: for each $v \in V$ there is $N_0 \in \mathbb Z$ with $v(\mathrm{diag}(y,1)) = 0$ whenever $\mathrm{v}(y) \le \exp(N_0)$. Let $w_J \in \mathrm{GL}_2(F)$ have matrix $\begin{pmatrix}0&1\\-1&0\end{pmatrix}$. Then, for the Borel structures on $F$ and on $\mathrm{GL}_2(F)$, for every Haar measure $\mu_2$ on $\mathrm{GL}_2(F)$, every open compact subgroup $\Omega$, every $g_0 \in \mathrm{GL}_2(F)$ and all $w_1, w_2 \in V$, the function
--   $$\Phi(X) = w_2(\mathrm{diag}(\det X, 1)) \cdot \Big(\int_\Omega w_1(g_0 k X^{-1})\, d\mu_2(k)\Big) \cdot |\det X|^{-1} \quad (\det X \neq 0), \qquad \Phi(X) = 0 \quad (\det X = 0)$$
--   on $M_2(F)$, with $|\cdot| =$ `modulus`, is locally constant with compact support, and for every $X$ with $\det X \neq 0$ its matrix Fourier transform `matFourier22` with respect to $\psi_p$ — the composite of the two column-wise Fourier transforms against the self-dual local Haar measure — satisfies
--   $$\widehat\Phi(X) = w_2(\mathrm{diag}(\det X, 1)\, w_J) \cdot \Big(\int_\Omega w_1(g_0 k X^{\mathsf T})\, d\mu_2(k)\Big) \cdot |\det X|^{-1} \, \theta_0(\det X)^{-1}.$$
--   No assertion is made about $\widehat\Phi$ on singular matrices.
--
--   This is the local Fourier-transform identity of Jacquet–Langlands (Lemma 13.1.1 of Automorphic Forms on GL(2)) for the Schwartz–Bruhat function on $M_2(F)$ built from a Kirillov function and an $\Omega$-averaged Whittaker matrix coefficient, here in the cuspidal case, with the Weyl element $w_J$ and transposition appearing on the dual side. It feeds the local Rankin–Selberg and Godement-type functional equations at $p$, being cited by the nodes establishing the cleared functional equation for the Godement zeta integral of a Whittaker vector and for the Rankin–Selberg local integrals attached to cuspidal and to principal-series data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_matFourier22_kirillov_det_mul_coefficient_eq_of_cuspidal.lean

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

theorem LanglandsTunnell.RankinSelberg.matFourier22_kirillov_det_mul_coefficient_eq_of_cuspidal
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

    (hcusp : ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ N₀ : ℤ, ∀ y : (p.adicCompletion ℚ)ˣ, Valued.v (y : (p.adicCompletion ℚ)) ≤ WithZero.exp N₀ → v (diagOne y) = 0)
    :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (Ω : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))), IsOpen (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))) → IsCompact (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∀ (g₀ : GL (Fin 2) (p.adicCompletion ℚ)),
      ∀ w₁ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        (IsLocallyConstant (fun X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) =>
        if h : X.det ≠ 0 then
          w₂ (diagOne (Units.mk0 X.det h)) *
            (∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w₁ (g₀ * k * (Matrix.GeneralLinearGroup.mkOfDetNeZero (X) (h))⁻¹) ∂μ₂) *
            (((modulus X.det : ℝ) : ℂ))⁻¹
        else 0) ∧
          HasCompactSupport (fun X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) =>
        if h : X.det ≠ 0 then
          w₂ (diagOne (Units.mk0 X.det h)) *
            (∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w₁ (g₀ * k * (Matrix.GeneralLinearGroup.mkOfDetNeZero (X) (h))⁻¹) ∂μ₂) *
            (((modulus X.det : ℝ) : ℂ))⁻¹
        else 0)) ∧
        ∀ (X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) (h : X.det ≠ 0),
          matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) (fun X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) =>
        if h : X.det ≠ 0 then
          w₂ (diagOne (Units.mk0 X.det h)) *
            (∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w₁ (g₀ * k * (Matrix.GeneralLinearGroup.mkOfDetNeZero (X) (h))⁻¹) ∂μ₂) *
            (((modulus X.det : ℝ) : ℂ))⁻¹
        else 0) X =
            w₂ (diagOne (Units.mk0 X.det h) * wJ) *
              (∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w₁ (g₀ * k * Matrix.GeneralLinearGroup.mkOfDetNeZero (X.transpose) (by rwa [Matrix.det_transpose])) ∂μ₂) *
              (((modulus X.det : ℝ) : ℂ))⁻¹ * (((θ₀ (Units.mk0 X.det h) : ℂˣ) : ℂ))⁻¹ := by sorry
