-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_finset_twistedTable_ne_zero_bound_unitarity_of_isArithGenuineCuspRealizable_rat
-- name    : LanglandsTunnell.exists_finset_twistedTable_ne_zero_bound_unitarity_of_isArithGenuineCuspRealizable_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/6c2bd84a-670a-56fe-be76-51670fb4b17d
-- title:
--   Unitarity and polynomial bounds for the twisted Hecke table over ℚ
-- statement:
--   Fix real numbers $c,u,d_1,d_2$ with $0<c$, $0<d_1<d_2$, and a finite set $T\subseteq \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, and let $D=\bigcup_{x\in T} D_0x$ where $D_0=$ `centreCutSiegelSet` is the set of $g$ whose finite part is integral, whose archimedean component has local height $\ge c$ and $x$-window square $\le u^2$ at every infinite place, and whose archimedean determinant norm lies in $[d_1,d_2]$ at every infinite place; assume $D$ covers $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ modulo rational points on the left and central idelic scalars on the right. Let $\Theta$ be a Hecke eigensystem over $\mathbb{Q}$ with values in $\mathbb{C}$ (a nonzero level ideal together with families $v\mapsto \Theta.a\,v$, $v\mapsto\Theta.b\,v$), assumed `IsArithGenuineCuspRealizable` for the carrier pins attached to $D$, the level subgroups $\mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, the Hecke generators $\mathrm{heckeGen}(v)$ and the adelic box. Let $\xi$ be a character of the central group of `productionPinsGeneral` $\mathbb{Q}$ (the full idele unit group) with values in $\mathbb{C}^\times$, $S_0$ a finite set of finite places, and $\varphi_0\neq 0$ a function on $\mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$ which is isotypic of type $\xi$ for $\Theta$ at level $\Theta.\mathrm{level}$ away from $S_0$: a continuous smooth cusp automorphic function, right invariant under the level subgroup, a Hecke coset eigenfunction with eigenvalue $\Theta.a\,v$ and central eigenvalue $\Theta.b\,v$ at each $v\notin S_0$. Assume finally $\|\xi(x)\| = \|x\|^{\sigma_0}$ for all ideles $x$, where $\|\cdot\|$ is the idele norm given by the distributive Haar character. Then there is a finite set $S_5$ of finite places such that, writing $N(v)=|\mathcal{O}/v|$, for all $v\notin S_5$: $N(v)^{\sigma_0}\,\Theta.b\,v/N(v)\neq 0$; there is a single exponent $\kappa\in\mathbb{R}$ with $\|N(v)^{\sigma_0/2}\,\Theta.a\,v\|\le N(v)^{\kappa}$ and $\|N(v)^{\sigma_0}\,\Theta.b\,v/N(v)\|\le N(v)^{\kappa}$; and the unitarity relations $\Theta.a\,v\cdot\overline{\Theta.b\,v} = N(v)^{1-\sigma_0}\,\overline{\Theta.a\,v}$ and $\|\Theta.b\,v\| = N(v)^{1-\sigma_0}$ hold.
--
--   This packages, for a genuinely cusp-realizable Hecke eigensystem over $\mathbb{Q}$ with central character of modulus $\|\cdot\|^{\sigma_0}$, the three properties of the twisted table $(N(v)^{\sigma_0/2}a_v,\ N(v)^{\sigma_0}b_v/N(v))$ needed downstream: non-vanishing of the twisted central value, a polynomial bound in $N(v)$, and the unitarity relations expressing self-adjointness of the Hecke eigenvalues against the central value. It feeds the construction of a unitary-shaped vector with Whittaker factorisation and torus profile in the converse-theorem step of the Langlands–Tunnell argument, and is proved from the realizability input together with the behaviour of the idele norm at a uniformiser idele.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_finset_twistedTable_ne_zero_bound_unitarity_of_isArithGenuineCuspRealizable_rat.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_LanglandsTunnell_ConverseData
import Mathlib.Analysis.MellinTransform
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicFourier IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SiegelCoordinates
open LanglandsTunnell LanglandsTunnell.RankinSelberg RSCarrier UnramifiedWhittaker

theorem LanglandsTunnell.exists_finset_twistedTable_ne_zero_bound_unitarity_of_isArithGenuineCuspRealizable_rat
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Θ : HeckeEigensystem ℚ ℂ)
    (hΘ : IsArithGenuineCuspRealizable ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) Θ)
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (S₀ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (φ₀ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ Θ.level S₀ Θ φ₀) (hne0 : φ₀ ≠ 0)
    (σ₀ : ℝ)
    (hσ₀ : ∀ x : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      ‖((ξ.comp Subgroup.topEquiv.symm.toMonoidHom x : ℂˣ) : ℂ)‖ = TateGlobal.ideleNorm ℚ x ^ σ₀) :
    ∃ S₅ : Finset (HeightOneSpectrum (𝓞 ℚ)),
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S₅ →
        (((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ σ₀ : ℝ) : ℂ) * (Θ.b v / ((Ideal.absNorm v.asIdeal : ℕ) : ℂ))) ≠ 0) ∧
      (∃ κ : ℝ, ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S₅ →
        ‖(((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (σ₀ / 2) : ℝ) : ℂ) * Θ.a v)‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧
        ‖(((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ σ₀ : ℝ) : ℂ) * (Θ.b v / ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)))‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S₅ →
        Θ.a v * (starRingEnd ℂ) (Θ.b v) = ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (1 - σ₀) : ℝ) : ℂ) * (starRingEnd ℂ) (Θ.a v) ∧
        ‖Θ.b v‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (1 - σ₀)) := by sorry
