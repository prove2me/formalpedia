-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_finite_mulSupport_and_continuous_and_exists_phase_finprod_dualWhittakerFn3_away
-- name    : LanglandsTunnell.RankinSelberg.finite_mulSupport_and_continuous_and_exists_phase_finprod_dualWhittakerFn3_away
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/e705bc98-facb-5e26-9518-08183cd040c6
-- title:
--   Finiteness, continuity and unit phase of dual Whittaker products
-- statement:
--   Fix a number field $K$, integral over $\mathbb{Q}$ in the sense that $\mathcal{O}_K$ is an integral $\mathcal{O}_\mathbb{Q}$-algebra, a carrier datum `pins` for $\mathbb{Q}$ (measurable spaces and measures on $\mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$ and on $\mathbb{A}_\mathbb{Q}$, a fundamental set, a central subgroup, level subgroups and local generators), an additive character $\psi$ of $\mathbb{A}_\mathbb{Q}$ whose inverse is the standard character [`NumberField.StandardAddChar.psiQ`](def/NumberField_StandardGlobalAddCharRat.html#L615), a homomorphism $\mu : (\mathbb{A}_K)^\times \to \mathbb{C}^\times$, and $F$ a `CubicInductionForm` for $(K,\mathrm{pins},\psi,\mu)$: a cuspidal automorphic form on $\mathrm{GL}_3(\mathbb{A}_\mathbb{Q})$ together with its global, local and archimedean Whittaker functions and its central character, subject to that structure's axioms (automorphy under $\mathrm{GL}_3(\mathbb{Q})$ and the central character law with idele class character, cuspidality along the two maximal parabolic radicals, the $\psi$-Whittaker integral law and the mirabolic expansion, the local $\psi_v$-Whittaker laws, factorisation of the global Whittaker function as the archimedean factor times the product of the local factors $W_v := F.\mathrm{whittakerLoc}\,v$ over any finite set containing all bad places, induced-spherical behaviour at the places that are not bad, invariance under the congruence subgroup $K_1$ of the induced level at places unramified in $K$, multiplicity one for the cyclic right-translation space of each $W_v$, moderate growth, $K$-finiteness of the archimedean factor, and the moment and half-plane integrability conditions; summarised here). Assume: $W_v(1) = 1$ at every finite place $v$ of $\mathbb{Q}$ not ramified in $K$ for which the level $\mathrm{addCharLevel}(\psi_v)$ vanishes; $\mathrm{addCharLevel}(\psi_v) = 0$ for every finite place $v$; and, for every finite set $T$ of finite places, at each $v \in T$ that is bad for $(K,\mu)$ (ramified in $K$, or $\mu$ ramified at some prime of $K$ above $v$) both that $W_v$ is right invariant under some open subgroup of $\mathrm{GL}_3(\mathbb{Q}_v)$ and that $W_v$ lies in the span of the right translates of every nonzero element of the span of its own right translates. Let $S'$ be a finite set of finite places containing all bad places, and $S_Q$ a finite set of finite places. Writing $D_v(Y) = 1$ for $v \in S_Q$ and $D_v(Y) = \widetilde{W_v}(\iota(Y_v))$ otherwise, where $\iota$ is the block embedding $\mathrm{GL}_2 \hookrightarrow \mathrm{GL}_3$ with last diagonal entry $1$, $Y_v$ is the component of $Y$ at $v$, and $\widetilde{W}(x) = W(w_3\,{}^t x^{-1})$ with $w_3$ the antidiagonal permutation matrix, the conclusion is fourfold: each $W_v$ is locally constant; for every $Y \in \mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$ the set of $v$ with $D_v(Y) \neq 1$ is finite; the map $g \mapsto \prod_v^{\mathrm{f}} D_v(g)$ is continuous on the subgroup of $\mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$ with trivial archimedean component; and for every adele $t$ and every $Y$ there is $\theta \in \mathbb{C}$ with $\|\theta\| = 1$ such that the product at $n(t)Y$, with $n(t)$ the upper unipotent $\begin{pmatrix}1 & t\\ 0 & 1\end{pmatrix}$, equals $\theta$ times the product at $Y$. The hypothesis that $S'$ contains all bad places is recorded but the displayed conclusion does not refer to $S'$.
--
--   This packages the analytic bookkeeping for the finite part of a Rankin–Selberg Euler product in the Whittaker model: local constancy of the local Whittaker factors, finiteness of the product away from the excluded set $S_Q$, continuity of the resulting function on the finite-adelic $\mathrm{GL}_2$, and the fact that left translation by a unipotent adele changes the product only by a complex number of modulus one. It feeds the integrability statements for the pure-tensor and hybrid Rankin–Selberg cell integrands used on the converse-theorem route to Langlands–Tunnell.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_finite_mulSupport_and_continuous_and_exists_phase_finprod_dualWhittakerFn3_away.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_HonestLDatum
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_LanglandsTunnell_LambdaSquared

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction MeasureTheory
open scoped nonZeroDivisors ENNReal
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open LanglandsTunnell.TateLocal UnramifiedWhittaker in
open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.finite_mulSupport_and_continuous_and_exists_phase_finprod_dualWhittakerFn3_away
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (F : CubicInductionForm K pins ψ μ)
    (hF1 : ∀ v, ¬ IsRamifiedIn K v → LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 → F.whittakerLoc v 1 = 1)
    (hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (hBad : ∀ T : Finset (HeightOneSpectrum (𝓞 ℚ)),
      (∀ v ∈ T, IsBadPlace K μ v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
        ∀ k ∈ Uv, ∀ g : LocalGL3 v, F.whittakerLoc v (g * k) = F.whittakerLoc v g) ∧
      (∀ v ∈ T, IsBadPlace K μ v → ∀ W ∈ gl3CyclicSubspace (F.whittakerLoc v), W ≠ 0 →
        F.whittakerLoc v ∈ gl3CyclicSubspace W))
    (S' : Finset (HeightOneSpectrum (𝓞 ℚ))) (hgood : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S' → ¬ IsBadPlace K μ p)
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    (∀ v : HeightOneSpectrum (𝓞 ℚ), IsLocallyConstant (F.whittakerLoc v)) ∧
    (∀ Y : AdelicGL2 (𝓞 ℚ) ℚ, (Function.mulSupport fun v : HeightOneSpectrum (𝓞 ℚ) =>
      if v ∈ SQ then (1 : ℂ) else dualWhittakerFn3 (F.whittakerLoc v) (iotaGL (localAt ℚ v Y))).Finite) ∧
    (Continuous fun g : finiteAdelicGL2Subgroup ℚ => ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
      if v ∈ SQ then (1 : ℂ) else dualWhittakerFn3 (F.whittakerLoc v) (iotaGL (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ)))) ∧
    (∀ (t : AdeleRing (𝓞 ℚ) ℚ) (Y : AdelicGL2 (𝓞 ℚ) ℚ), ∃ θ : ℂ, ‖θ‖ = 1 ∧
      (∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), if v ∈ SQ then (1 : ℂ) else
          dualWhittakerFn3 (F.whittakerLoc v) (iotaGL (localAt ℚ v (unipotentGL2 t * Y)))) =
        θ * ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), if v ∈ SQ then (1 : ℂ) else
          dualWhittakerFn3 (F.whittakerLoc v) (iotaGL (localAt ℚ v Y))) := by sorry
