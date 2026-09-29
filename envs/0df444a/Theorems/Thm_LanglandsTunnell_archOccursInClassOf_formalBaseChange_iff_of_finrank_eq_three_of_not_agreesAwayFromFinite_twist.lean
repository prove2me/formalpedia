-- Prove2me | Theorems.Thm_LanglandsTunnell_archOccursInClassOf_formalBaseChange_iff_of_finrank_eq_three_of_not_agreesAwayFromFinite_twist
-- name    : LanglandsTunnell.archOccursInClassOf_formalBaseChange_iff_of_finrank_eq_three_of_not_agreesAwayFromFinite_twist
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/d1f3a9eb-7b26-5919-abb9-9c7d2d9e382e
-- title:
--   Cubic base change: archimedean types and weight-one holomorphy
-- statement:
--   Let $K$ be a number field with $[K:\mathbb Q]=3$ and with $\mathcal O_K$ an integral $\mathcal O_{\mathbb Q}$-algebra. Over $\mathbb Q$ fix reals $c',u',d_1',d_2'$ with $d_1'<d_2'$ and a finite set $T'\subset GL_2(\mathbb A_{\mathbb Q})$ such that the union $D'$ of the right translates by the $x\in T'$ of `centreCutSiegelSet ℚ c' u' d₁' d₂'` (matrices with integral finite part, local height $\ge c'$ at every infinite place, window $\le u'^2$, and archimedean determinant norms in $[d_1',d_2']$) satisfies `CoversModCentre`: every element of $GL_2(\mathbb A_{\mathbb Q})$ can be brought into $D'$ by left multiplication by a global point and right multiplication by a central scalar. Fix data $c,u,d_1,d_2,T$ over $K$ of the same shape with $d_1<d_2$ and covering set $D$. Let $\Phi$ be a complex Hecke eigensystem over $\mathbb Q$ such that its central renormalisation `Φ.toRawCentral` admits a smooth cusp realization with continuous underlying function at the production pins built on $D'$ (adelic Haar measures, full centre, levels `levelOne ⊓ finiteAdelicGL2Subgroup`, Hecke generators `heckeGen`, the adelic box as conditioning set), and assume some eigensystem over $K$ agreeing outside a finite set of primes with `formalBaseChange ℚ K Φ` (level $\top$, with $a_{\mathfrak P}=$ `satakePow` of the inertia degree applied to $(a_v,b_v)$ and $b_{\mathfrak P}=b_v^{f}$, $v=\mathfrak P\cap\mathcal O_{\mathbb Q}$) is likewise realizable at the pins built on $D$. Fix a finite set $S_0$ of primes of $\mathcal O_{\mathbb Q}$ and $\chi$ on primes with values in $\mathbb C$ such that $\chi(v)^2=1$ for $v\notin S_0$, and for $v\notin S_0$ one has $\chi(v)=1$ exactly when no prime of $K$ above $v$ has inertia degree $2$; assume $\Phi$ does not agree away from a finite set of primes with `Φ.twist χ`. Then for every real place $w$ of $K$ three equivalences hold, where `ArchOccursInClassOf F D Θ P` asserts that some eigensystem agreeing with $\Theta$ outside a finite set of primes has a continuous smooth cusp realization at the pins built on $D$ whose underlying function satisfies $P$: first, for every homomorphism $\chi'$ from `rowIsometrySubgroup₀ ℝ` to $\mathbb C^\times$, the class of `formalBaseChange ℚ K Φ` on $D$ contains a function satisfying `HasArchCharacterAt₀` at $w$ for $\chi'$ transported along the real isomorphism `ringEquivRealOfIsReal hw` if and only if the class of $\Phi$ on $D'$ contains a function satisfying the corresponding condition at every real place of $\mathbb Q$; second, the same equivalence with the weight-one character `archWeightOneAt` in place of $\chi'$ and with the additional requirement `IsArchHolomorphicAt` (for every $g$, the function $z\mapsto (\operatorname{Im}z)^{-1}\varphi(g\cdot \iota_w(\text{Iwasawa section of }z))$ is holomorphic on the upper half-plane) imposed at $w$ on the $K$-side and at the infinite place of $\mathbb Q$ on the $\mathbb Q$-side; third, the same equivalence with holomorphy negated on both sides.
--
--   This is the class-level form of cubic base change for $GL_2$ with archimedean compatibility at the real places, in the Langlands–Tunnell part of the argument: it matches the archimedean row-isometry types, and the weight-one holomorphic and non-holomorphic cases, of a cuspidal class over $\mathbb Q$ and of its formal cubic base change. It feeds the construction of a genuine weight-one holomorphic realization attached to the base change of a non-self-twist eigensystem over a cubic field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_archOccursInClassOf_formalBaseChange_iff_of_finrank_eq_three_of_not_agreesAwayFromFinite_twist.lean

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_FormalBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel
  AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem LanglandsTunnell.archOccursInClassOf_formalBaseChange_iff_of_finrank_eq_three_of_not_agreesAwayFromFinite_twist
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (c' u' d₁' d₂' : ℝ) (T' : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hd' : d₁' < d₂')
    (hcov' : CoversModCentre ℚ (⋃ x ∈ T', (· * x) '' centreCutSiegelSet ℚ c' u' d₁' d₂'))
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ)
    (hΦ : IsArithGenuineCuspRealizable ℚ
      (productionPinsOf ℚ (⋃ x ∈ T', (· * x) '' centreCutSiegelSet ℚ c' u' d₁' d₂')
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      Φ)
    (hcuspK : ∃ Ψ : HeckeEigensystem K ℂ, Ψ.AgreesAwayFromFinite (formalBaseChange ℚ K Φ) ∧
      IsArithGenuineCuspRealizable K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        Ψ)
    (S₀ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (χ : HeightOneSpectrum (𝓞 ℚ) → ℂ)
    (_hχ2 : ∀ v ∉ S₀, χ v * χ v = 1)
    (_hlink : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S₀ →
      (χ v = 1 ↔ ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) = v →
        (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal ≠ 2))
    (_hnd : ¬ HeckeEigensystem.AgreesAwayFromFinite Φ (Φ.twist χ)) :
    ∀ w : InfinitePlace K, ∀ hw : w.IsReal,
      (∀ χ' : rowIsometrySubgroup₀ ℝ →* ℂˣ,
        ArchOccursInClassOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) (formalBaseChange ℚ K Φ)
            (fun φ => HasArchCharacterAt₀ K w
              (χ'.comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
                (norm_ringEquivRealOfIsReal hw))) φ) ↔
          ArchOccursInClassOf ℚ (⋃ x ∈ T', (· * x) '' centreCutSiegelSet ℚ c' u' d₁' d₂') Φ
            (fun φ => ∀ w' : InfinitePlace ℚ, ∀ hw' : w'.IsReal, HasArchCharacterAt₀ ℚ w'
              (χ'.comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw')
                (norm_ringEquivRealOfIsReal hw'))) φ)) ∧
      (ArchOccursInClassOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) (formalBaseChange ℚ K Φ)
          (fun φ => HasArchCharacterAt₀ K w (archWeightOneAt hw) φ ∧ IsArchHolomorphicAt w hw φ) ↔
        ArchOccursInClassOf ℚ (⋃ x ∈ T', (· * x) '' centreCutSiegelSet ℚ c' u' d₁' d₂') Φ
          (fun φ => (∀ w' : InfinitePlace ℚ, ∀ hw' : w'.IsReal,
              HasArchCharacterAt₀ ℚ w' (archWeightOneAt hw') φ) ∧
            IsArchHolomorphicAt Rat.infinitePlace Rat.isReal_infinitePlace φ)) ∧
      (ArchOccursInClassOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) (formalBaseChange ℚ K Φ)
          (fun φ => HasArchCharacterAt₀ K w (archWeightOneAt hw) φ ∧ ¬ IsArchHolomorphicAt w hw φ) ↔
        ArchOccursInClassOf ℚ (⋃ x ∈ T', (· * x) '' centreCutSiegelSet ℚ c' u' d₁' d₂') Φ
          (fun φ => (∀ w' : InfinitePlace ℚ, ∀ hw' : w'.IsReal,
              HasArchCharacterAt₀ ℚ w' (archWeightOneAt hw') φ) ∧
            ¬ IsArchHolomorphicAt Rat.infinitePlace Rat.isReal_infinitePlace φ)) := by sorry
