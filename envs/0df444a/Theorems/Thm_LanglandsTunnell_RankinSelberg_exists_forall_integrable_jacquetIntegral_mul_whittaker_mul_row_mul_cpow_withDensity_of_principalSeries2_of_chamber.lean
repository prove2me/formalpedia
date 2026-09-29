-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_jacquetIntegral_mul_whittaker_mul_row_mul_cpow_withDensity_of_principalSeries2_of_chamber
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_integrable_jacquetIntegral_mul_whittaker_mul_row_mul_cpow_withDensity_of_principalSeries2_of_chamber
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/0facdc5a-2976-587d-be57-b50685bd276f
-- title:
--   Integrability of the folded local Rankin–Selberg integrand in the chamber
-- statement:
--   Let $p$ be a nonzero prime ideal of $\mathcal O_{\mathbb Q}$ and write $F$ for the completion $\mathbb Q_p$ and $\psi =$ `psiLocal` for the standard additive character of $F$ obtained from the global standard character. Let $\mu_0,\mu_1$ be locally constant homomorphisms $F^\times \to \mathbb C^\times$ and $\sigma_0,\sigma_1$ reals with $\|\mu_i(a)\| = \|a\|^{\sigma_i}$ for all $a$, and assume the chamber condition $\sigma_1 < \sigma_0$. Let $\varphi : \mathrm{GL}_2(F) \to \mathbb C$ lie in `principalSeries2 p μ`, i.e. $\varphi$ is locally constant, invariant under left translation by the upper unipotent matrices $\begin{pmatrix}1&x\\0&1\end{pmatrix}$, and satisfies $\varphi(\mathrm{diag}(a)g) = \mathrm{torusChar2}(a)\,\mathrm{halfModulus2}(a)\,\varphi(g)$ for $a \in (F^\times)^2$. Let $\Phi_2 : F \times F \to \mathbb C$ be locally constant with compact support. Let $\theta_0 : F^\times \to \mathbb C^\times$ be a homomorphism, $N \neq 0$ an ideal of $\mathcal O_{\mathbb Q}$, and let $w_2^\flat : \mathrm{GL}_2(F) \to \mathbb C$ satisfy: $w_2^\flat(n(x)g) = \psi(x)\,w_2^\flat(g)$ for the unipotent $n(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$; right invariance under [`AdelicDock.localLevelOne`](def/AdelicDock_LocalEmbedding.html#L178), the pullback along the local embedding of $\mathrm{GL}_2(F)$ into $\mathrm{GL}_2$ of the finite adeles of the finite level-one subgroup of level $N$; admissibility, namely for every open subgroup $U \le \mathrm{GL}_2(F)$ there is a finite set $B$ of functions such that every element of the $\mathbb C$-span of the right translates $g \mapsto w_2^\flat(gh)$ which is right $U$-invariant lies in the span of $B$; and the central character law $w_2^\flat(z\cdot g) = \theta_0(z)\,w_2^\flat(g)$ for scalar matrices $z \in F^\times$. Equip $\mathrm{GL}_2(F)$ and $F$ with their Borel $\sigma$-algebras. Then for every Haar measure $\mu_2$ on $\mathrm{GL}_2(F)$, every Haar measure $\mu_{N_2}$ on the range of `unipotentGL2Hom` (the subgroup of matrices $n(x)$), and every $w_2$ in the $\mathbb C$-span of the right translates of $w_2^\flat$, there exists $\sigma_2 \in \mathbb R$ such that for every $s \in \mathbb C$ with $\sigma_2 < \mathrm{Re}\,s$ the function
--   $$g \mapsto \Bigl(\int_F \psi(x)\,\varphi\bigl(w_0\,n(x)\,g\bigr)\,d\mu_{\mathrm{sd}}(x)\Bigr)\cdot w_2(g)\,\Phi_2(g_{10},g_{11})\cdot \bigl(\mathrm{modulus}(\det g)\bigr)^{s + 1/2 - 1/2}$$
--   is integrable with respect to $\mu_2$ weighted by the density [`HaarQuotient.density`](def/HaarQuotient.html#L25) of the unipotent subgroup for $\mu_{N_2}$. Here $w_0$ is the antidiagonal matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$, $\mu_{\mathrm{sd}}$ is the self-dual Haar measure `selfDualHaarAt` on $F$ (the additive Haar measure of the ring of integers scaled by $(\mathrm{absNorm}\,p)^{-\mathrm{level}(\psi)/2}$), $\mathrm{modulus}$ is the module of $F$ given by the distributive Haar character, and the density is $g \mapsto \mathrm{weight}(g)\big/\int_{N_2}\mathrm{weight}(ng)\,d\mu_{N_2}(n)$ for the auxiliary weight function of `HaarQuotient`.
--
--   This is the convergence half of the local $(2,2)$ Rankin–Selberg integral at a finite place: it asserts that the folded integrand built from the Jacquet integral of a principal-series vector in the chamber $\sigma_1 < \sigma_0$, a Whittaker vector in the span of right translates of an admissible $\psi$-Whittaker function with central character, and a Schwartz–Bruhat function on the second row, is genuinely Bochner integrable for the $N_2$-quotient-weighted Haar measure when $\mathrm{Re}\,s$ is large. It is used by the statements computing the local integral as a rational function of $q^{-s}$ and establishing its functional equation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_jacquetIntegral_mul_whittaker_mul_row_mul_cpow_withDensity_of_principalSeries2_of_chamber.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_forall_integrable_jacquetIntegral_mul_whittaker_mul_row_mul_cpow_withDensity_of_principalSeries2_of_chamber
    (p : HeightOneSpectrum (𝓞 ℚ))

    (μ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hμ : ∀ i, IsLocallyConstant (μ i))
    (σ : Fin 2 → ℝ)
    (hσ : ∀ (i : Fin 2) (a : (p.adicCompletion ℚ)ˣ), ‖((μ i a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (σ i))
    (h01 : σ 1 < σ 0)
    (φ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ : φ ∈ principalSeries2 p μ)

    (Φ₂ : p.adicCompletion ℚ × p.adicCompletion ℚ → ℂ) (hΦ₂ : IsLocallyConstant Φ₂ ∧ HasCompactSupport Φ₂)

    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
          (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
        ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          ∃ σ₂ : ℝ, ∀ s : ℂ, σ₂ < s.re →
            Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                ((fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                    φ (antidiagonal2 p * upperUnipotent2 p x * g) ∂(selfDualHaarAt ℚ p)) g * (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  w₂ g * Φ₂ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)) g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) := by sorry
