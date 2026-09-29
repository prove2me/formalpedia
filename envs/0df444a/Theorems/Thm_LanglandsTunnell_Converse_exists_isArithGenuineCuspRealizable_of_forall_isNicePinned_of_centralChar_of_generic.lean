-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_exists_isArithGenuineCuspRealizable_of_forall_isNicePinned_of_centralChar_of_generic
-- name    : LanglandsTunnell.Converse.exists_isArithGenuineCuspRealizable_of_forall_isNicePinned_of_centralChar_of_generic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/7d7802de-199f-5bad-a44f-9747d44aa7b2
-- title:
--   Converse theorem for GL(2) with pinned root number and central character
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be real numbers with $c>0$ and $d_1>0$, and let $T$ be a finite set of elements of $\mathrm{GL}_2(\mathbb{A}_K)$; write $P_T$ for the carrier pins `productionPinsOf` attached to the union of the right translates $\{g x : g \in \mathrm{centreCutSiegelSet}\ K\ c\ u\ d_1\ d_2\}$ for $x \in T$, to the level groups $N \mapsto \mathrm{levelOne}(N) \sqcap \ker(\mathrm{glArch})$, to the Hecke generators $\mathrm{heckeGen}(v)$ and to the adelic box (with the Borel–Haar measures on $\mathrm{GL}_2(\mathbb{A}_K)$ and the Haar measure conditioned on the box on $\mathbb{A}_K$, and $Z = \top$). Let $\Pi$ be a Hecke eigensystem over $K$ with complex coefficients (a nonzero level ideal together with families $a_v, b_v$ over the finite places), $S$ a finite set of finite places, $\mathrm{archR}$, $\mathrm{archC}$ archimedean parameters at the real and complex places, $\varepsilon_v$ a character of $K_v^\times$ for each finite place, continuous for $v \in S$, and $A, A^{d} \colon \mathbb{Z}^{S} \to \mathbb{C}$. Assume: (i) for every ideal $N$ of $\mathcal{O}_K$ and every finite place $v$ with $v \nmid N$ there are $\#(\mathcal{O}_K/v)+1$ representatives of the cosets of $U(N) = \mathrm{levelOne}(N) \sqcap \ker(\mathrm{glArch})$ in the double coset $U(N)\,\mathrm{heckeGen}(v)\,U(N)$, in the sense of `IsHeckeCosetSystem` (all representatives lie in the double coset, every element of it is congruent to one of them modulo $U(N)$ on the right, and they are pairwise incongruent); (ii) $A$ and $A^{d}$ are bounded by a common constant, both vanish at every $n$ with $n_v < n_{0,v}$ for some $v$, for one and the same $n_0 \in \mathbb{Z}^{S}$, and $A \neq 0$; (iii) for every continuous unitary idele class character $\mu$ of $\mathbb{A}_K^\times$ whose local component at each $v \in S$ is inverse to $\varepsilon_v$ on the units of valuation $1$, and for all archimedean twisting data $u_R, a_R, u_C, k_C$ realising the archimedean components of $\mu$ in the sense of `IsArchCompAt`, the $L$-datum $\mathrm{twistedDatum}$ built from $\Pi$, $\mathrm{archR}$, $\mathrm{archC}$, $\mu$ and these data is `IsNicePinned` with respect to the $S$-part series $\mathrm{sPart}(A,\mu)$, $\mathrm{sPartDual}(A^{d},\mu)$, the root number $\mathrm{pinnedRootNumber}$ and the conductor $\mathrm{finiteConductor}(\mu,S)$: the datum is well formed and convergent, the conductor is positive, and there are entire functions bounded on vertical strips agreeing with the two completed series in the half-plane $\mathrm{Re}\,s > 1$ and related by the functional equation $\Lambda(s) = \varepsilon\,N^{1/2-s}\,\Lambda^{d}(1-s)$; (iv) $\Pi$ does not agree, outside some finite set of places, with any Eisenstein eigensystem $a_v = \mu_1(\pi_v)+\mu_2(\pi_v)$, $b_v = \mu_1(\pi_v)\mu_2(\pi_v)$ for continuous idele class characters $\mu_1,\mu_2$; (v) $\omega$ is a continuous unitary idele class character, unramified outside $S$, with $\omega(\pi_v) = b_v$ for $v \notin S$, whose archimedean components are given by the central exponent and central sign (respectively central twist) of $\mathrm{archR}$ and $\mathrm{archC}$; (vi) genericity: $a_v^2 \neq b_v(q_v + 2 + q_v^{-1})$ for $v \notin S$, together with the stated exclusions on the differences of the parameters of $\mathrm{archR}$ at principal real places and of $\mathrm{archC}$ at complex places. Then there is a Hecke eigensystem $\Phi'$ over $K$ with complex coefficients such that the eigensystem obtained from $\Phi'$ by replacing $b_v$ with $(\mathrm{cNorm}\,v)^{-1} b_v$ admits a genuine cuspidal realization at $P_T$, and $\Phi'$ has the same $a_v$ and $b_v$ as $\Pi$ for all but finitely many finite places.
--
--   This is the converse theorem for $\mathrm{GL}(2)$ over a number field in the form of Jacquet–Langlands: niceness of all unitary twists of the $L$-functions attached to a system of Hecke parameters, with root number, conductor and central character pinned, produces a cuspidal automorphic realization whose Hecke parameters agree with the given ones outside a finite set. It is used in the Langlands–Tunnell step, where the $L$-functions of the relevant two-dimensional representation and its twists are shown to be nice and a cuspidal form agreeing with a base-change datum is required.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_exists_isArithGenuineCuspRealizable_of_forall_isNicePinned_of_centralChar_of_generic.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_ConverseData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal
open AutomorphicForm.WindowedSiegel

theorem LanglandsTunnell.Converse.exists_isArithGenuineCuspRealizable_of_forall_isNicePinned_of_centralChar_of_generic
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
      IsArchCompAt K ω w (archC w hw).centralExponent (archC w hw).centralTwist) :
    ∃ Φ' : HeckeEigensystem K ℂ,
      IsArithGenuineCuspRealizable K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        Φ' ∧
        HeckeEigensystem.AgreesAwayFromFinite Pi Φ' := by sorry
