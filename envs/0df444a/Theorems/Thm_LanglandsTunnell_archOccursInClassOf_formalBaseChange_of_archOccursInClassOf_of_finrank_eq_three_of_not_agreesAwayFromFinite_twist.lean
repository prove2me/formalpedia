-- Prove2me | Theorems.Thm_LanglandsTunnell_archOccursInClassOf_formalBaseChange_of_archOccursInClassOf_of_finrank_eq_three_of_not_agreesAwayFromFinite_twist
-- name    : LanglandsTunnell.archOccursInClassOf_formalBaseChange_of_archOccursInClassOf_of_finrank_eq_three_of_not_agreesAwayFromFinite_twist
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/62b09cb5-d7f8-5b12-875f-2df1ff93c60f
-- title:
--   Cubic base change: archimedean class-level ascent, non-self-twist case
-- statement:
--   Let $K$ be a number field with $[K:\mathbb{Q}]=3$, equipped with an algebra structure $\mathcal{O}_{\mathbb{Q}}\to\mathcal{O}_K$ making $\mathcal{O}_K$ integral over $\mathcal{O}_{\mathbb{Q}}$. Over $\mathbb{Q}$ fix reals $c',u',d_1',d_2'$ with $d_1'<d_2'$ and a finite set $T'$ of adelic matrices, and put $D'=\bigcup_{x\in T'}\,\mathfrak{S}'x$, where $\mathfrak{S}'=$ `centreCutSiegelSet ℚ c' u' d₁' d₂'` consists of those $g$ whose finite part is integral, with local height at least $c'$ and $x$-window at most $u'^2$ at every infinite place and archimedean determinant norms in $[d_1',d_2']$; assume $D'$ covers modulo the centre, i.e. every adelic $g$ has $\gamma g z\in D'$ for some global $\gamma\in GL_2(\mathbb{Q})$ and some central adelic scalar $z$. Fix data $c,u,d_1,d_2,T$ over $K$ with $d_1<d_2$ and the analogous covering property for $D=\bigcup_{x\in T}\mathfrak{S}x$. Let $\Phi$ be a complex Hecke eigensystem over $\mathbb{Q}$ (a nonzero level ideal together with functions $a,b$ on the primes). Assume that some eigensystem $\Psi$ over $K$ agreeing with the formal base change `formalBaseChange ℚ K Φ` (whose values at $\mathfrak{P}$ are $\mathrm{satakePow}$ of the inertia degree $f(\mathfrak{P}\mid v)$ applied to $(a_v,b_v)$, and $b_v^{\,f}$) outside a finite set of primes satisfies `IsArithGenuineCuspRealizable` for the production pins built from $D$, the levels `levelOne` intersected with the kernel of the archimedean projection, the Hecke generators `heckeGen` and the box `adelicBox`; that is, $\Psi$ after the `toRawCentral` normalisation admits a continuous smooth cusp realisation there. Fix a finite set $S_0$ of primes of $\mathbb{Q}$ and $\chi$ from primes to $\mathbb{C}$ such that $\chi(v)^2=1$ for $v\notin S_0$, such that for $v\notin S_0$ one has $\chi(v)=1$ if and only if no prime $\mathfrak{P}$ of $K$ above $v$ has inertia degree $2$, and such that $\Phi$ does not agree outside a finite set of primes with its twist $v\mapsto(\chi(v)a_v,\chi(v)^2b_v)$. The conclusion is that for every real place $w$ of $K$ four implications hold, each of the form: if an archimedean condition occurs in the near-equivalence class of $\Phi$ on $D'$, then the corresponding condition at $w$ occurs in the class of `formalBaseChange ℚ K Φ` on $D$. Here `ArchOccursInClassOf F D Θ P` means that some eigensystem agreeing with $\Theta$ outside a finite set of primes admits, after the `toRawCentral` normalisation, a continuous smooth cusp realisation at the production pins over $D$ whose underlying function satisfies $P$. The four conditions are: (i) for each homomorphism $\chi'$ from `rowIsometrySubgroup₀ ℝ` to $\mathbb{C}^\times$, the predicate `HasArchCharacterAt₀` for $\chi'$ transported by `ringEquivRealOfIsReal` at every real place of $\mathbb{Q}$, ascending to the same predicate at $w$; (ii) the weight-one character `archWeightOneAt` at all real places of $\mathbb{Q}$ together with `IsArchHolomorphicAt` at the infinite place of $\mathbb{Q}$ (for all $g$, $z\mapsto(\operatorname{Im}z)^{-1}\varphi(g\cdot\text{Iwasawa section})$ is holomorphic on the upper half-plane), ascending to weight one and holomorphy at $w$; (iii) the same with holomorphy negated on both sides; (iv) for each $\chi'$, the transported character condition at all real places of $\mathbb{Q}$ together with `IsArchLowestWeightAt` (holomorphy of $z\mapsto(\operatorname{Im}z)^{\sigma}\varphi(g\cdot\text{Iwasawa section})$ for some $\sigma\in\mathbb{C}$), ascending to the corresponding pair at $w$.
--
--   This is the scoped, class-level form of cubic base change for $GL_2$ together with its archimedean compatibility — Langlands' cyclic base change when $K/\mathbb{Q}$ is Galois, and the non-normal cubic lifting of Jacquet, Piatetski-Shapiro and Shalika otherwise — stated for eigensystems that are not isomorphic, away from finitely many primes, to their twist by the resolvent sign character $\chi$. It is obtained from the corresponding statement with Casimir data and feeds the biconditional version [`LanglandsTunnell.archOccursInClassOf_formalBaseChange_iff_of_finrank_eq_three_of_not_agreesAwayFromFinite_twist`](thm.html#LanglandsTunnell.archOccursInClassOf_formalBaseChange_iff_of_finrank_eq_three_of_not_agreesAwayFromFinite_twist), which in turn serves the Langlands–Tunnell input to modularity of residual representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_archOccursInClassOf_formalBaseChange_of_archOccursInClassOf_of_finrank_eq_three_of_not_agreesAwayFromFinite_twist.lean

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_ArchLowestWeight

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel
  AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem LanglandsTunnell.archOccursInClassOf_formalBaseChange_of_archOccursInClassOf_of_finrank_eq_three_of_not_agreesAwayFromFinite_twist
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
        ArchOccursInClassOf ℚ (⋃ x ∈ T', (· * x) '' centreCutSiegelSet ℚ c' u' d₁' d₂') Φ
            (fun φ => ∀ w' : InfinitePlace ℚ, ∀ hw' : w'.IsReal, HasArchCharacterAt₀ ℚ w'
              (χ'.comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw')
                (norm_ringEquivRealOfIsReal hw'))) φ) →
          ArchOccursInClassOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) (formalBaseChange ℚ K Φ)
            (fun φ => HasArchCharacterAt₀ K w
              (χ'.comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
                (norm_ringEquivRealOfIsReal hw))) φ)) ∧
      (ArchOccursInClassOf ℚ (⋃ x ∈ T', (· * x) '' centreCutSiegelSet ℚ c' u' d₁' d₂') Φ
          (fun φ => (∀ w' : InfinitePlace ℚ, ∀ hw' : w'.IsReal,
              HasArchCharacterAt₀ ℚ w' (archWeightOneAt hw') φ) ∧
            IsArchHolomorphicAt Rat.infinitePlace Rat.isReal_infinitePlace φ) →
        ArchOccursInClassOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) (formalBaseChange ℚ K Φ)
          (fun φ => HasArchCharacterAt₀ K w (archWeightOneAt hw) φ ∧ IsArchHolomorphicAt w hw φ)) ∧
      (ArchOccursInClassOf ℚ (⋃ x ∈ T', (· * x) '' centreCutSiegelSet ℚ c' u' d₁' d₂') Φ
          (fun φ => (∀ w' : InfinitePlace ℚ, ∀ hw' : w'.IsReal,
              HasArchCharacterAt₀ ℚ w' (archWeightOneAt hw') φ) ∧
            ¬ IsArchHolomorphicAt Rat.infinitePlace Rat.isReal_infinitePlace φ) →
        ArchOccursInClassOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) (formalBaseChange ℚ K Φ)
          (fun φ => HasArchCharacterAt₀ K w (archWeightOneAt hw) φ ∧ ¬ IsArchHolomorphicAt w hw φ)) ∧
      (∀ χ' : rowIsometrySubgroup₀ ℝ →* ℂˣ,
        ArchOccursInClassOf ℚ (⋃ x ∈ T', (· * x) '' centreCutSiegelSet ℚ c' u' d₁' d₂') Φ
            (fun φ => (∀ w' : InfinitePlace ℚ, ∀ hw' : w'.IsReal, HasArchCharacterAt₀ ℚ w'
              (χ'.comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw')
                (norm_ringEquivRealOfIsReal hw'))) φ) ∧
              IsArchLowestWeightAt Rat.infinitePlace Rat.isReal_infinitePlace φ) →
          ArchOccursInClassOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) (formalBaseChange ℚ K Φ)
            (fun φ => HasArchCharacterAt₀ K w
              (χ'.comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
                (norm_ringEquivRealOfIsReal hw))) φ ∧ IsArchLowestWeightAt w hw φ)) := by sorry
