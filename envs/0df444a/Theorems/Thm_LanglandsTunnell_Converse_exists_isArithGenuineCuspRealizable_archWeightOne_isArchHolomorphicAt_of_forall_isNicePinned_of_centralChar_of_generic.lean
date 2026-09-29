-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_exists_isArithGenuineCuspRealizable_archWeightOne_isArchHolomorphicAt_of_forall_isNicePinned_of_centralChar_of_generic
-- name    : LanglandsTunnell.Converse.exists_isArithGenuineCuspRealizable_archWeightOne_isArchHolomorphicAt_of_forall_isNicePinned_of_centralChar_of_generic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/ee79bad9-a85d-5427-8a0f-bcc2340c2a02
-- title:
--   Converse theorem with pinned constants and weight-one real components
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be reals with $c>0$ and $d_1>0$, let $T$ be a finite set of elements of $\mathrm{GL}_2(\mathbb{A}_K)$, let $\Pi$ be a complex Hecke eigensystem over $K$ (a nonzero level ideal together with families $a_v,b_v$ indexed by the finite places), let $S$ be a finite set of finite places, let $\mathrm{archR}_w$ be a real archimedean parameter at each real place and $\mathrm{archC}_w$ a complex one at each complex place, and let $\varepsilon_v:(K_v)^\times\to\mathbb{C}^\times$ be characters, continuous for $v\in S$. Write $\mathrm{pins}$ for the carrier pins with Haar measure and Borel structure on $\mathrm{GL}_2(\mathbb{A}_K)$, carrier $D=\bigcup_{x\in T}(\cdot\,x)\,[\,\text{centre-cut Siegel set of parameters }c,u,d_1,d_2]$, central subgroup $Z=\top$, level subgroups $U(N)=\mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, Hecke elements $\mathrm{heckeGen}(v)$, and the adelic box conditioned additive measure. The hypotheses are: for every ideal $N$ and every $v\nmid N$ the double coset of $\mathrm{heckeGen}(v)$ modulo $U(N)$ admits a system of exactly $\mathrm{N}v+1$ representatives (`IsHeckeCosetSystem`); coefficient families $A,A^\vee:\mathbb{Z}^S\to\mathbb{C}$ that are uniformly bounded and vanish outside a translate of $\mathbb{N}^S$, with $A\neq 0$; for every continuous unitary character $\mu$ of $\mathbb{A}_K^\times/K^\times$ satisfying $\mu_v\varepsilon_v=1$ on units of valuation $1$ for $v\in S$, and every archimedean data $(u_R,a_R,u_C,k_C)$ realising the archimedean components of $\mu$ by `IsArchCompAt`, the twisted $L$-datum of $\Pi\otimes\mu$ outside $S$ is nice with $S$-parts $\mathrm{sPart}(A,\mu)$, $\mathrm{sPartDual}(A^\vee,\mu)$, root number $\mathrm{pinnedRootNumber}$ and conductor $\mathrm{finiteConductor}(\mu,S)$, that is: the datum is well-formed and convergent, the conductor is positive, and there are entire functions $\Lambda,\Lambda^\vee$, bounded on vertical strips, agreeing for $\mathrm{Re}\,s>1$ with the products of the $S$-part, the archimedean factor and the $L$-function (respectively their duals), and satisfying $\Lambda(s)=\varepsilon\,N^{1/2-s}\Lambda^\vee(1-s)$; $\Pi$ agrees away from no finite set with any Eisenstein eigensystem $a_v=\mu_1(\pi_v)+\mu_2(\pi_v)$, $b_v=\mu_1(\pi_v)\mu_2(\pi_v)$ built from continuous idele class characters; a continuous unitary idele class character $\omega$, unramified outside $S$ with $\omega(\pi_v)=\Pi.b\,v$ for $v\notin S$ and with archimedean components given by the central exponents and central signs/twists of $\mathrm{archR}$, $\mathrm{archC}$; the genericity conditions $a_v^2\neq b_v(\mathrm{N}v+2+\mathrm{N}v^{-1})$ for $v\notin S$ and the stated non-degeneracy of the real and complex archimedean parameters; and, at each real place, $\mathrm{archR}_w=\mathrm{principal}\,0\,a_1\,0\,a_2$ with $a_1\neq a_2$. The conclusion is the existence of a complex Hecke eigensystem $\Phi'$ over $K$ and a smooth cusp realization $R$ at $\mathrm{pins}$ of $\Phi'.\mathrm{toRawCentral}$ (same $a_v$, with $b_v$ replaced by $(\mathrm{N}v)^{-1}b_v$) — so $R$ is a nonzero $U(\Phi'.\mathrm{level})$-invariant smooth cusp form with a central character on $Z$, which is a Hecke eigenfunction with eigenvalues $a_v$ and satisfies the central eigenvalue relation outside a finite set — such that $R$ is continuous, at each real place $w$ it carries the archimedean character `archWeightOneAt hw` in the sense of `HasArchCharacterAt₀`, and for every $g$ the function $z\mapsto (\mathrm{Im}\,z)^{-1}R(g\cdot\iota_w(\mathrm{iwasawaSectionGL}\,z))$ is holomorphic on the upper half-plane; moreover $\Pi$ and $\Phi'$ have the same $a_v$ and $b_v$ outside a finite set of places.
--
--   This is the converse theorem for $\mathrm{GL}_2$ over a number field in a form with pinned root number, conductor and central character, whose conclusion additionally records that the cuspidal realization obtained is holomorphic of weight one at every real place. It is the analytic input used to produce a weight-one automorphic form with prescribed Hecke eigenvalues from an odd two-dimensional Artin-type datum, and is cited in that deduction within the Langlands–Tunnell step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_exists_isArithGenuineCuspRealizable_archWeightOne_isArchHolomorphicAt_of_forall_isNicePinned_of_centralChar_of_generic.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_LanglandsTunnell_ConverseData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal
open AutomorphicForm.WindowedSiegel

theorem LanglandsTunnell.Converse.exists_isArithGenuineCuspRealizable_archWeightOne_isArchHolomorphicAt_of_forall_isNicePinned_of_centralChar_of_generic
    (K : Type) [Field K] [NumberField K] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁)
    (Pi : HeckeEigensystem K ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (hepsS : ∀ v ∈ S, Continuous ⇑(epsS v))
    (A Ad : (↥S → ℤ) → ℂ)
    (hsys : ∀ (N : Ideal (𝓞 K)) (v : HeightOneSpectrum (𝓞 K)), ¬ v.asIdeal ∣ N →
      ∃ reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 K) K,
        HeckeIntegralSeam.IsHeckeCosetSystem
          ((productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).U N)
          (heckeGen (𝓞 K) K v) reps)
    (hbd : ∃ C : ℝ, ∀ n : ↥S → ℤ, ‖A n‖ ≤ C ∧ ‖Ad n‖ ≤ C)
    (hsupp : ∃ n₀ : ↥S → ℤ, ∀ n : ↥S → ℤ, (∃ v, n v < n₀ v) → A n = 0 ∧ Ad n = 0)
    (hA0 : A ≠ 0)
    (hnice : ∀ μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ, IsAdmissibleTwist K μ →
      (∀ v ∈ S, ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 →
        localChar μ v u * epsS v u = 1) →
      ∀ (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ)
        (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
        (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ)
        (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ),
        (∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ)) →
        (∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw)) →
        IsNicePinned (twistedDatum K Pi S archR archC μ uR aR uC kC)
          (sPart K S A μ) (sPartDual K S Ad μ)
          (pinnedRootNumber K Pi μ S archR archC uR aR uC kC) (finiteConductor K μ S))
    (hnonEis : ∀ (μ₁ μ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
      IsIdeleClassChar (𝓞 K) K μ₁ → IsIdeleClassChar (𝓞 K) K μ₂ →
      Continuous μ₁ → Continuous μ₂ →
      ¬ HeckeEigensystem.AgreesAwayFromFinite Pi
          (eisensteinTableOf K Pi.level Pi.level_ne_bot μ₁ μ₂))
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hω : IsAdmissibleTwist K ω)
    (hωunr : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → IsUnramifiedCharAt ω v)
    (hωb : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ((ω (uniformizerIdele K v) : ℂˣ) : ℂ) = Pi.b v)
    (hgen : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      Pi.a v ^ 2 ≠ Pi.b v * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) + 2 + ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)⁻¹))
    (hgenR : ∀ (w : InfinitePlace K) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
      archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ →
        ∀ p : ℤ, p ≠ 0 → u₁ - u₂ = (p : ℂ) → a₁ - a₂ ≠ ((p + 1 : ℤ) : ZMod 2))
    (hgenC : ∀ (w : InfinitePlace K) (hw : w.IsComplex) (p q : ℕ), 1 ≤ p → 1 ≤ q →
      ¬ ((2 * ((archC w hw).u₁ - (archC w hw).u₂) = ((p + q : ℕ) : ℂ) ∧
            (archC w hw).k₁ - (archC w hw).k₂ = (p : ℤ) - q) ∨
          (2 * ((archC w hw).u₁ - (archC w hw).u₂) = -((p + q : ℕ) : ℂ) ∧
            (archC w hw).k₁ - (archC w hw).k₂ = (q : ℤ) - p)))
    (hωR : ∀ (w : InfinitePlace K) (hw : w.IsReal),
      IsArchCompAt K ω w (archR w hw).centralExponent ((archR w hw).centralSign.val : ℤ))
    (hωC : ∀ (w : InfinitePlace K) (hw : w.IsComplex),
      IsArchCompAt K ω w (archC w hw).centralExponent (archC w hw).centralTwist)
    (harchR₁ : ∀ (w : InfinitePlace K) (hw : w.IsReal),
      ∃ a₁ a₂ : ZMod 2, a₁ ≠ a₂ ∧ archR w hw = RealArchParam.principal 0 a₁ 0 a₂) :
    ∃ Φ' : HeckeEigensystem K ℂ,
      (∃ R : SmoothCuspRealizationAt K
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K))
          Φ'.toRawCentral,
        IsGenuineCuspRealizationAt K
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K))
          Φ'.toRawCentral R ∧
        (∀ w : InfinitePlace K, ∀ hw : w.IsReal, HasArchCharacterAt₀ K w (archWeightOneAt hw) R.toFun) ∧
        (∀ w : InfinitePlace K, ∀ hw : w.IsReal, IsArchHolomorphicAt w hw R.toFun)) ∧
      HeckeEigensystem.AgreesAwayFromFinite Pi Φ' := by sorry
