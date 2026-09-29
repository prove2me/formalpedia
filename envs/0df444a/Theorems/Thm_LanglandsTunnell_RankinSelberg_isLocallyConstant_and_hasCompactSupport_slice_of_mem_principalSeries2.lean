-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_isLocallyConstant_and_hasCompactSupport_slice_of_mem_principalSeries2
-- name    : LanglandsTunnell.RankinSelberg.isLocallyConstant_and_hasCompactSupport_slice_of_mem_principalSeries2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/1c1773ac-e063-506e-a7a5-62eda904569b
-- title:
--   Local Godement slice is locally constant with compact support
-- statement:
--   Let $p$ be a height-one prime of the ring of integers of $\mathbb{Q}$, so that $\mathbb{Q}_p =$ `p.adicCompletion ℚ`. Let $\lambda_0,\lambda_1 \colon \mathbb{Q}_p^\times \to \mathbb{C}^\times$ be locally constant group homomorphisms, and $\chi \colon \mathbb{Q}_p^\times \to \mathbb{C}^\times$ a further locally constant homomorphism. Let $F \colon \mathrm{GL}_2(\mathbb{Q}_p) \to \mathbb{C}$ lie in `principalSeries2 p lam`, that is: $F$ is locally constant, $F\left(\begin{pmatrix}1&x\\0&1\end{pmatrix}g\right) = F(g)$ for all $x \in \mathbb{Q}_p$ and all $g$, and $F(\mathrm{diag}(a_0,a_1)g) = \lambda_0(a_0)\lambda_1(a_1)\,\sqrt{\|a_0\|/\|a_1\|}\,F(g)$ for all units $a_0,a_1$ and all $g$. Let $\Phi \colon M_2(\mathbb{Q}_p) \to \mathbb{C}$ be locally constant with compact support. With $\mathbb{Q}_p$ and $\mathrm{GL}_2(\mathbb{Q}_p)$ carrying their Borel $\sigma$-algebras, the assertion is that for every Haar measure $\mu_2$ on $\mathrm{GL}_2(\mathbb{Q}_p)$ the function $$\phi(a,d) = \int_{K} F(k)\,\chi(\det k)\left(\int_{\mathbb{Q}_p} \Phi\!\left(\begin{pmatrix}a&x\\0&d\end{pmatrix}k\right)dx\right) d\mu_2(k)$$ on $\mathbb{Q}_p \times \mathbb{Q}_p$ is locally constant and has compact support. Here $K$ is the level-one subgroup [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤`](def/AdelicDock_LocalEmbedding.html#L178), the pullback along the local embedding [`AdelicDock.localEmbed`](def/AdelicDock_LocalEmbedding.html#L97) of the adelic level-one subgroup of level $\top$, and $dx$ is the self-dual Haar measure `selfDualHaarAt ℚ p`, namely the additive Haar measure giving $\mathbb{Z}_p$ volume one, rescaled by $(\#(\mathcal{O}/p))^{-n/2}$ where $n$ is the level of the standard additive character at $p$. No integrability hypothesis is imposed; the integrals are Bochner integrals, taking the value $0$ where the integrand fails to be integrable.
--
--   This is the local regularity input for Godement's unfolding of the principal-series Godement–Jacquet zeta integral at a finite place: the inner $x$-integral over the unipotent variable, averaged over the maximal compact against a principal-series vector twisted by $\chi \circ \det$, produces a Schwartz–Bruhat function of the two diagonal variables. It feeds the two-variable local Tate theory step, and is used in the proof that the Godement zeta integral of a principal-series vector equals a product with a two-variable zeta integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_isLocallyConstant_and_hasCompactSupport_slice_of_mem_principalSeries2.lean

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

theorem LanglandsTunnell.RankinSelberg.isLocallyConstant_and_hasCompactSupport_slice_of_mem_principalSeries2
    (p : HeightOneSpectrum (𝓞 ℚ))
    (lam : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i))
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (F : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hF : F ∈ principalSeries2 p lam)
    (Φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
        let ϕ : (p.adicCompletion ℚ) × (p.adicCompletion ℚ) → ℂ := fun ad =>
          ∫ k in (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set (GL (Fin 2) (p.adicCompletion ℚ))),
            F k * ((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) *
              (∫ x : (p.adicCompletion ℚ), Φ (!![ad.1, x; 0, ad.2] * (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) ∂(selfDualHaarAt ℚ p)) ∂μ₂
        IsLocallyConstant ϕ ∧ HasCompactSupport ϕ := by sorry
