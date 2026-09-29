-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_godementUnfold_of_principalSeries2_of_admissible_ed2
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_integrable_godementUnfold_of_principalSeries2_of_admissible_ed2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/9d054439-092c-5594-a0b3-165f16d2419b
-- title:
--   Absolute convergence of the unfolded local Godement integrand
-- statement:
--   Fix a nonzero prime $p$ of $\mathcal O_{\mathbb Q}$ and write $F = \mathbb Q_p$ for the completion $p$-adically. Let $\mu_0,\mu_1 : F^\times \to \mathbb C^\times$ be locally constant characters and $\sigma_0,\sigma_1$ real numbers with $\|\mu_i(a)\| = \|a\|^{\sigma_i}$ for all $a$, and $\sigma_1 < \sigma_0$; let $\varphi : GL_2(F) \to \mathbb C$ lie in `principalSeries2 p μ`, that is, $\varphi$ is locally constant, left invariant under the upper unipotent matrices $\begin{pmatrix}1&x\\0&1\end{pmatrix}$, and satisfies $\varphi(\mathrm{diag}(a_0,a_1)g) = \mathrm{torusChar2}(a)\cdot\mathrm{halfModulus2}(a)\cdot\varphi(g)$. Let $\chi : F^\times\to\mathbb C^\times$ be locally constant, $\varphi_1$ a locally constant compactly supported function on $M_2(F)$, and $\varphi_2$ one on $F^2$. Let $\theta : F^\times\to\mathbb C^\times$ be a character and $w : GL_2(F)\to\mathbb C$ a function with $w\big(\begin{pmatrix}1&a\\0&1\end{pmatrix}g\big) = \psi_p(a)\,w(g)$ for the local standard additive character $\psi_p$, right invariant under some open subgroup, admissible in the sense that for every open subgroup $U$ there is a finite set $B$ of functions such that every right $U$-invariant element of the $\mathbb C$-span of the right translates $g\mapsto w(gh)$ lies in the span of $B$, and with central behaviour $w(z\cdot 1_2\, g) = \theta(z)w(g)$. Equip $GL_2(F)$ and $F$ with their Borel $\sigma$-algebras. Then for every Haar measure $\mu_2$ on $GL_2(F)$, every Haar measure $\mu_{N_2}$ on the subgroup of matrices $\begin{pmatrix}1&x\\0&1\end{pmatrix}$ (the range of `unipotentGL2Hom`), and every Haar measure $\nu$ on $GL_2(F)$, two assertions hold. First, there is $\sigma'$ such that for all $s$ with $\sigma' < \operatorname{Re} s$ the function $$(g,h)\longmapsto \varphi_1(h)\,\chi(\det h)\,|\det h|^{s+1/2}\cdot W'(g)\,w(gh)\,\varphi_2(g_{10},g_{11})\,|\det g|^{s},$$ where $W'(g) = \int_F \psi_p(x)\,\varphi(w_0\,n(x)\,g)\,dx$ is taken against the self-dual Haar measure on $F$ with $w_0 = \begin{pmatrix}0&1\\1&0\end{pmatrix}$ and $n(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$, and $|\cdot|$ denotes the module of $F$, is integrable for the product of $\nu$ with $\mu_2$ weighted by the density [`HaarQuotient.density`](def/HaarQuotient.html#L25) attached to the unipotent subgroup and $\mu_{N_2}$. Second, for every $w'$ in the span of the right translates of $w$ there is $\sigma'$ such that for $\sigma' < \operatorname{Re} s$ the function $g \mapsto W'(g)\,w'(g)\,\varphi_2(g_{10},g_{11})\,|\det g|^{s+1/2-1/2}$ is integrable for $\mu_2$ weighted by that same density.
--
--   This is the absolute convergence statement accompanying the local Godement unfolding of the $GL_3\times GL_2$ Rankin–Selberg integral of Jacquet, Piatetski-Shapiro and Shalika, in the form needed at the non-archimedean place $p$, with the Whittaker partner $w$ taken abstractly (a $\psi_p$-Whittaker function with open stabiliser, admissible span of right translates and a central character) rather than as a vector in a fixed irreducible representation. It feeds the computation of the local Rankin–Selberg integral for the Jacquet–Whittaker function of a principal series, used in the converse-theorem input to the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_godementUnfold_of_principalSeries2_of_admissible_ed2.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_forall_integrable_godementUnfold_of_principalSeries2_of_admissible_ed2
    (p : HeightOneSpectrum (𝓞 ℚ))

    (μ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hμ : ∀ i, IsLocallyConstant (μ i))
    (σ : Fin 2 → ℝ)
    (hσ : ∀ (i : Fin 2) (a : (p.adicCompletion ℚ)ˣ), ‖((μ i a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (σ i))
    (h01 : σ 1 < σ 0)
    (φ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ : φ ∈ principalSeries2 p μ)

    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)

    (φ₁ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ₁ : IsLocallyConstant φ₁ ∧ HasCompactSupport φ₁)
    (φ₂ : (p.adicCompletion ℚ) × (p.adicCompletion ℚ) → ℂ) (hφ₂ : IsLocallyConstant φ₂ ∧ HasCompactSupport φ₂)

    (θ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hwlaw : ∀ (a : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (unipotent a * g) = NumberField.StandardAddChar.psiLocal ℚ p a * w g)
    (hwsm : ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
      ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g)
    (hwadm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w' (g * k) = w' g) →
            w' ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hcentral : ∀ (zc : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (Matrix.GeneralLinearGroup.scalar (Fin 2) zc * g) = ((θ zc : ℂˣ) : ℂ) * w g)
    :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := (p.adicCompletion ℚ))).range) [μN₂.IsHaarMeasure]
      (ν : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [ν.IsHaarMeasure],

    (∃ σ' : ℝ, ∀ s : ℂ, σ' < s.re →
        Integrable (fun gh : GL (Fin 2) (p.adicCompletion ℚ) × GL (Fin 2) (p.adicCompletion ℚ) =>
            (φ₁ (gh.2 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det gh.2) : ℂˣ) : ℂ) *
                ((modulus ((Matrix.GeneralLinearGroup.det gh.2 : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2)) *
              ((∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
                φ (antidiagonal2 p * upperUnipotent2 p x * gh.1) ∂(selfDualHaarAt ℚ p)) *
                w (gh.1 * gh.2) *
                φ₂ ((gh.1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (gh.1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) *
                ((modulus ((Matrix.GeneralLinearGroup.det gh.1 : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ s))
          ((μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)).prod ν)) ∧

    (∀ w' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)),
      ∃ σ' : ℝ, ∀ s : ℂ, σ' < s.re →
        Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          ((fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              ∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
                φ (antidiagonal2 p * upperUnipotent2 p x * g) ∂(selfDualHaarAt ℚ p)) g *
            (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              w' g * φ₂ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)) g) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂))) := by sorry
