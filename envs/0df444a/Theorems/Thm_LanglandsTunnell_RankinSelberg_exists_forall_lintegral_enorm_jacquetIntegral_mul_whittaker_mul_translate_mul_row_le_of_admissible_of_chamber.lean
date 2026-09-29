-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_lintegral_enorm_jacquetIntegral_mul_whittaker_mul_translate_mul_row_le_of_admissible_of_chamber
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_lintegral_enorm_jacquetIntegral_mul_whittaker_mul_translate_mul_row_le_of_admissible_of_chamber
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/30351909-d6c8-585d-9f39-6678295d41ae
-- title:
--   Inner bound for the local Rankin–Selberg N₂backslash GL₂ integral
-- statement:
--   Let $p$ be a finite place of $\mathbb{Q}$, written as a height-one prime of $\mathcal{O}_{\mathbb{Q}}$, and put $F = \mathbb{Q}_p$ for the corresponding completion. Let $\mu_0,\mu_1 : F^\times \to \mathbb{C}^\times$ be locally constant characters and $\sigma_0,\sigma_1$ reals with $|\mu_i(a)| = \|a\|^{\sigma_i}$ for all $a$, and assume the chamber condition $\sigma_1 < \sigma_0$. Let $\varphi : GL_2(F) \to \mathbb{C}$ lie in `principalSeries2`, i.e. $\varphi$ is locally constant, invariant under left translation by the upper unipotents $\begin{pmatrix}1&x\\0&1\end{pmatrix}$, and satisfies $\varphi(\mathrm{diag}(a)g) = \mathrm{torusChar2}(a)\,\mathrm{halfModulus2}(a)\,\varphi(g)$ for diagonal matrices with unit entries. Let $\theta : F^\times \to \mathbb{C}^\times$ be a character, and let $w : GL_2(F) \to \mathbb{C}$ satisfy: the Whittaker law $w(\begin{pmatrix}1&a\\0&1\end{pmatrix}g) = \psi_p(a)\,w(g)$ for the standard local additive character $\psi_p$; right invariance under some open subgroup of $GL_2(F)$; the admissibility condition that for every open subgroup $U$ there is a finite set $B$ of functions such that every element of the span of the right translates $g \mapsto w(gh)$ which is right $U$-invariant lies in the span of $B$; and the central character condition $w(z\cdot g) = \theta(z)w(g)$ for scalar $z \in F^\times$. Let $\varphi_2 : F \times F \to \mathbb{C}$ be locally constant with compact support. The assertion, with $GL_2(F)$ and $F$ carrying their Borel structures, is the existence of reals $\sigma_0', \tau$ and a natural number $A$, independent of all further data, such that for every Haar measure $\mu_2$ on $GL_2(F)$, every Haar measure $\mu_{N_2}$ on the image $N_2$ of $x \mapsto \begin{pmatrix}1&x\\0&1\end{pmatrix}$, and every real $\sigma' > \sigma_0'$, there is $I \ge 0$ with the following property for all $g_0 \in GL_2(F)$: the lower integral, against $\mu_2$ weighted by the density [`HaarQuotient.density`](def/HaarQuotient.html#L25) of $N_2$ relative to $\mu_{N_2}$, of $$\bigl\|W'(g)\,w(gg_0)\,\varphi_2(g_{10},g_{11})\bigr\|\cdot\|\det g\|^{\sigma'},\qquad W'(g) = \int_F \psi_p(x)\,\varphi\!\left(\begin{pmatrix}0&1\\1&0\end{pmatrix}\begin{pmatrix}1&x\\0&1\end{pmatrix}g\right) dx$$ (the inner integral taken against the self-dual Haar measure of $F$ attached to $\psi_p$) is at most $$I \cdot \max\bigl(\|g_0\|^{\tau}, (\|\det g_0\|/\|g_0\|)^{\tau}\bigr) \cdot \max\bigl(1, ((\|\det g_0\|/\|g_0\|^2)^A)^{-1}\bigr),$$ where $\|g_0\|$ denotes the maximum of the absolute values of the four entries of $g_0$. Thus the bound depends on $g_0$ only through $\|g_0\|$ and $\|\det g_0\|$.
--
--   This is the local convergence estimate for the $GL_2 \times GL_2$ Rankin–Selberg integral in the form of Jacquet–Piatetski-Shapiro–Shalika §6.3: the $N_2\backslash GL_2$-integral of the majorised integrand is finite for $\sigma'$ large, with a bound uniform in the translation parameter $g_0$ up to the stated gauge factors. It feeds the integrability statements for the Godement-type unfolding and for the Jacquet integral against a Whittaker function, which in turn underlie the local theory used in the converse-theorem step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_lintegral_enorm_jacquetIntegral_mul_whittaker_mul_translate_mul_row_le_of_admissible_of_chamber.lean

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

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.RankinSelberg
open MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

theorem LanglandsTunnell.RankinSelberg.exists_forall_lintegral_enorm_jacquetIntegral_mul_whittaker_mul_translate_mul_row_le_of_admissible_of_chamber
    (p : HeightOneSpectrum (𝓞 ℚ))

    (μ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hμ : ∀ i, IsLocallyConstant (μ i))
    (σ : Fin 2 → ℝ)
    (hσ : ∀ (i : Fin 2) (a : (p.adicCompletion ℚ)ˣ), ‖((μ i a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (σ i))
    (h01 : σ 1 < σ 0)
    (φ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ : φ ∈ principalSeries2 p μ)

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
    (φ₂ : (p.adicCompletion ℚ) × (p.adicCompletion ℚ) → ℂ) (hφ₂ : IsLocallyConstant φ₂ ∧ HasCompactSupport φ₂) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    ∃ (σ₀' τ : ℝ) (A : ℕ), ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := (p.adicCompletion ℚ))).range) [μN₂.IsHaarMeasure] (σ' : ℝ), σ₀' < σ' →
      ∃ I : ℝ, 0 ≤ I ∧ ∀ g₀ : GL (Fin 2) (p.adicCompletion ℚ),
        ∫⁻ g : GL (Fin 2) (p.adicCompletion ℚ),
            ‖(∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
                φ (antidiagonal2 p * upperUnipotent2 p x * g) ∂(selfDualHaarAt ℚ p)) *
              w (g * g₀) * φ₂ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)‖₊ *
            ENNReal.ofReal (‖((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))‖ ^ σ')
          ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)) ≤
        ENNReal.ofReal (I *
          max ((max (max ‖((g₀ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 0‖ ‖((g₀ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1‖) (max ‖((g₀ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0‖ ‖((g₀ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1‖)) ^ τ) ((‖((Matrix.GeneralLinearGroup.det g₀ : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))‖ / max (max ‖((g₀ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 0‖ ‖((g₀ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1‖) (max ‖((g₀ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0‖ ‖((g₀ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1‖)) ^ τ) *
          max 1 (((‖((Matrix.GeneralLinearGroup.det g₀ : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))‖ / (max (max ‖((g₀ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 0‖ ‖((g₀ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1‖) (max ‖((g₀ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0‖ ‖((g₀ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1‖)) ^ 2) ^ A)⁻¹)) := by sorry
