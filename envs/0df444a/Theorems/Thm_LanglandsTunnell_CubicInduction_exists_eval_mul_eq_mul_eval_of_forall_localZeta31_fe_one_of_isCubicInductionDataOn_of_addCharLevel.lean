-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_eval_mul_eq_mul_eval_of_forall_localZeta31_fe_one_of_isCubicInductionDataOn_of_addCharLevel
-- name    : LanglandsTunnell.CubicInduction.exists_eval_mul_eq_mul_eval_of_forall_localZeta31_fe_one_of_isCubicInductionDataOn_of_addCharLevel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/2e7a11a8-67dd-5fce-8f0a-b87681e4a359
-- title:
--   Local functional equation at v matches induced Euler polynomials
-- statement:
--   The setting is a cubic field $K$ together with a character of its idele class group, a cubic induction datum on $\mathbb{Q}$, and a $\gamma$-factor datum at one distinguished finite place.
--
--   **Global data.** $K$ is a number field with $\operatorname{finrank}_{\mathbb{Q}} K = 3$ (hypothesis `_hdeg`), equipped with an $\mathcal{O}_{\mathbb{Q}}$-algebra structure on $\mathcal{O}_K$ which is integral. Next, $\psi$ is an additive character of the adele ring of $\mathbb{Q}$ which is global in the sense of `IsGlobalAddChar` (`_h\psi`): it is trivial on the image of $\mathbb{Q}$, continuous, and not identically $1$. Further, $\mu : \mathbb{A}_K^{\times} \to \mathbb{C}^{\times}$ is an admissible twist (`_h\mu`), i.e. trivial on the principal ideles $K^{\times}$, continuous and unitary. A finite place $w$ of $\mathbb{Q}$ is *bad* for $(K,\mu)$ when either $w$ is ramified in $K$ (some prime of $\mathcal{O}_K$ in the fibre over $w$ has ramification index $\neq 1$) or $\mu$ is ramified at some prime of that fibre. Hypothesis `_hlev` requires that at every finite place $v$ of $\mathbb{Q}$ which is not bad the local component $\mathrm{psiLoc}\,\psi\,v$ has `addCharLevel` equal to $0$. Hypothesis `_hns` is a non-descent condition: there is no admissible twist $\eta$ of $\mathbb{Q}$ such that for every prime $\mathfrak{P}$ of $\mathcal{O}_K$ at which $\mu$ is unramified and with $\eta$ unramified at the prime $\mathfrak{p}$ of $\mathbb{Q}$ below, one has $\mu(\varpi_{\mathfrak{P}}) = \eta(\varpi_{\mathfrak{p}})^{f}$, where $\varpi$ denotes the uniformizer idele and $f = \mathrm{inertiaDeg}'(\mathfrak{p},\mathfrak{P})$.
--
--   **Carrier data.** A set $D$ in the adelic $GL_2$ of $\mathbb{Q}$, a level map $U$ from ideals of $\mathcal{O}_{\mathbb{Q}}$ to subgroups of adelic $GL_2$, and a family `gen` of adelic $GL_2$ elements indexed by finite places assemble into the carrier pins `productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)`, which carries the Borel structures and the adelic Haar measure on $GL_2$, the full central subgroup, and the additive adelic Haar measure conditioned on the adelic box. A finite set $S$ of finite places of $\mathbb{Q}$ is assumed, by `hSbad`, to consist of exactly the bad places.
--
--   **The datum $X$.** $X$ is a `CubicInductionData`, that is, a tuple consisting of a function `X.form` on adelic $GL_3$ over $\mathbb{Q}$, a global Whittaker function `X.whittaker`, local Whittaker functions `X.whittakerLoc v` on $GL_3(\mathbb{Q}_v)$ for each finite place, an archimedean Whittaker function `X.whittakerArch` on $GL_3$ of the infinite adeles, a central character `X.centralChar` on the ideles, and a dual Whittaker function `X.dualWhittaker`. The hypothesis `hX` asserts `IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ S X`; its clauses (summarised here) state that `X.form` is invariant under $GL_3(\mathbb{Q})$ on the left and transforms by `X.centralChar` under the adelic centre, that `X.centralChar` is an idele class character, that `X.form` is cuspidal along the two parabolics $P_{21}$ and $P_{12}$ of the pins, that `X.whittaker` is the $\psi$-Whittaker integral of `X.form` and satisfies the $\psi$-Whittaker transformation law, that the mirabolic translates of `X.whittaker` sum to `X.form`, that each `X.whittakerLoc v` satisfies the $\mathrm{psiLoc}\,\psi\,v$-Whittaker law and has multiplicity one, that `X.whittaker` factorises as `X.whittakerArch` of the archimedean component times the product of the `X.whittakerLoc v` over any finite set containing $S$ outside which the component lies in the maximal compact subgroup, that outside $S$ each `X.whittakerLoc v` is induced-spherical for the coefficient system `inducedCoeff K μ` (right invariance under the maximal compact, two Hecke coset eigenvalue equations with eigenvalues $N_v \cdot \mathrm{inducedE}_i$, and the central relation with $\mathrm{inducedE}_3$) and, at unramified places outside $S$, is invariant under the congruence subgroup `congruenceK1` of level `inducedLevelAt K μ v`, that `X.form` has moderate growth, `X.whittakerArch` is $K$-finite, `X.form` has iota moments and `X.whittaker` has a Whittaker half-plane, and the corresponding dual statements for `X.dualWhittaker`, the $\psi^{-1}$-Whittaker integral of `dualForm X.form`.
--
--   **Analytic hypotheses on $X$.** `hcont`: `X.form` is continuous; `hW` and `hW'`: `X.whittaker` and `X.dualWhittaker` are gauge-majorised in the sense of `IsGaugeMajorised3` (vanishing outside a root-level region and bounded there by $C$ divided by a power of the root-size product times an arbitrary power of $1+$ the archimedean root sum); `hcontW`, `hcontW'`: both are continuous. A constant $c \in \mathbb{C}$ is given with $c$ times the volume of the adelic box for the adelic additive Haar measure equal to $1$ (`hc`).
--
--   **Normalisation and bad-place package.** `hexp`: `X.form` is not identically zero, and for every finite place $v$ which is not bad and at which $\mathrm{psiLoc}\,\psi\,v$ has level $0$, one has $X.\mathrm{whittakerLoc}\,v\,(1) = 1$ and `HasSphericalTorusValuesAt (inducedCoeff K μ) v (X.whittakerLoc v)`, the explicit evaluation of the local Whittaker function at the torus points `iotaTorusLocal v n` and at the two-row points in terms of $N_v^{-n}$ and the `sphericalTorusValue`s of the induced parameters $\mathrm{inducedE}_1, \mathrm{inducedE}_2, \mathrm{inducedE}_3$. `hbad`: for every finite set $T$ of places, at each bad $v \in T$ the function `X.whittakerLoc v` is right invariant under some open subgroup of $GL_3(\mathbb{Q}_v)$, and every non-zero element $W$ of the cyclic subspace `gl3CyclicSubspace (X.whittakerLoc v)` (the span of the right translates) has `X.whittakerLoc v` in `gl3CyclicSubspace W`.
--
--   **The distinguished place and local hypotheses at $S$.** A place $v \in S$ is fixed (`hv`). `h1`: $X.\mathrm{whittakerLoc}\,w\,(1) = 1$ for all $w \in S$ with $w \neq v$. `hadm`: for each $w \in S$ and each open subgroup $U_w$ of $GL_3(\mathbb{Q}_w)$ there is a finite set $B$ of functions whose $\mathbb{C}$-span contains every $U_w$-right-invariant element of `gl3CyclicSubspace (X.whittakerLoc w)`. `hcent`: for each $w \in S$ the local component of `X.centralChar` at $w$ is unitary, and `X.whittakerLoc w` transforms by it under the scalar matrices. `hψw`: $\mathrm{psiLoc}\,\psi\,w$ has level $0$ for all $w \in S$.
--
--   **Global integrability.** `hS` and `hS'`: for every admissible twist $\tau$ of $\mathbb{Q}$ and every $g$ in adelic $GL_3$ there is $\sigma_0$ such that for $\operatorname{Re} s > \sigma_0$ the two global zeta integrands are integrable for the $S$-part measure $\nu_S$ of [`NumberField.Idele.productMeasureData ℚ S`](def/NumberField_IdeleProductMeasure.html#L679), namely $a \mapsto X.\mathrm{whittaker}(\iota(\mathrm{diag}(a,1))g)\,\tau(a)\,\|a\|^{s-1}$ in `hS`, and in `hS'` the analogous integrand in which the Whittaker value is replaced by the archimedean integral of `dualWhittakerFn3 X.whittakerArch` along the lower unipotent direction times the product over $v \in S$ of the local integrals of `dualWhittakerFn3 (X.whittakerLoc v)` along the lower unipotent direction, each normalised by the inverse self-dual measure of the local integers.
--
--   **Data at $v$.** `hKv`: $v$ is not ramified in $K$; `hψv`: $\mathrm{psiLoc}\,\psi\,v$ has level $0$. A monoid homomorphism $E$ from the units of the infinite adeles of $\mathbb{Q}$ to the ideles is given together with `hE`: the infinite part of $E u$ is $u$ and the finite part is $1$, so $E$ splits the projection to the archimedean ideles. A Haar measure $\nu_{\mathrm{mul}}$ on the units of the infinite adeles is fixed. `harch` asserts archimedean non-vanishing: there exist $g_\infty \in GL_3$ of the infinite adeles and an admissible twist $\sigma$ of $\mathbb{Q}$ together with $t \in \mathbb{C}$ and $e \in \mathbb{Z}$ such that $\sigma$ has archimedean type $(t,e)$ at every real place in the sense of `IsArchCompAt`, such that the value at $-1$ of the trivial character of $(\mathbb{Q}_v)^{\times}$ equals $(-1)^{e}$, and such that for every $\sigma_0$ there is $s$ with $\operatorname{Re} s > \sigma_0$ and $\mathrm{archZeta30}\,\nu_{\mathrm{mul}}\,(h \mapsto X.\mathrm{whittakerArch}(h g_\infty))\,(\sigma \circ E)\,s\,1 \neq 0$.
--
--   **The $\gamma$-factor datum at $v$.** Non-zero polynomials $R_1, R_2 \in \mathbb{C}[X]$ and an integer $m$ are given. Writing $N_v = \operatorname{absNorm} v$, hypothesis `hFE1` states that for every $g \in GL_3(\mathbb{Q}_v)$ there exist polynomials $Q_1, Q_2$ with $Q_2 \neq 0$, an integer $n$ and reals $\sigma_0, \sigma_1$ such that: the $GL_3 \times GL_1$ local zeta integral `localZeta30` at $v$ of `X.whittakerLoc v` against the trivial character, for the multiplicative measure obtained from the self-dual additive Haar measure at $v$, converges for $\operatorname{Re} s > \sigma_0$; for such $s$,
--   $$\mathrm{localZeta30}(s,g)\, Q_2(N_v^{-s}) = Q_1(N_v^{-s})\, N_v^{\,n s};$$
--   the dual integral `IsLocalZeta31ConvergentAbove` for `dualWhittakerFn3 (X.whittakerLoc v)` against the inverse of the trivial character at $\mathrm{weylPrime3} \cdot \mathrm{transposeInv3}\,g$ converges above $\sigma_1$; and for all $s$ with $\sigma_1 < \operatorname{Re}(1-s)$,
--   $$\mathrm{localZetaDual31}(1-s, g)\,\bigl(Q_2(N_v^{-s})R_2(N_v^{-s})\bigr) = R_1(N_v^{-s})\,Q_1(N_v^{-s})\,N_v^{\,(m+n)s}.$$
--   Thus $R_1, R_2, m$ form a $g$-independent $\gamma$-factor datum for the trivial character at $v$.
--
--   **Conclusion.** There exists $\varepsilon \in \mathbb{C}$ with $\varepsilon \neq 0$ such that for every $s \in \mathbb{C}$
--   $$R_1(N_v^{-s})\, N_v^{\,m s}\, E^{\vee}\bigl(N_v^{-(1-s)}\bigr) = \varepsilon\, N_v^{\,\ell(1/2-s)}\, E\bigl(N_v^{-s}\bigr)\, R_2(N_v^{-s}),$$
--   where $E = \mathrm{inducedEulerPoly}\ \mathbb{Q}\ (\mathrm{inducedCoeff}\ K\ \mu)\ v$ and $E^{\vee} = \mathrm{inducedEulerPoly}\ \mathbb{Q}\ (\mathrm{inducedCoeff}\ K\ \mu^{-1})\ v$ are the finite products over the primes of $\mathcal{O}_K$ in the fibre above $v$ of the induced local factors attached to the Frobenius values of $\mu$, respectively $\mu^{-1}$, at unramified primes (and $0$ at ramified ones), and $\ell = \mathrm{inducedLevelAt}\ K\ \mu\ v = \sum_{\mathfrak{P} \mid v} f(\mathfrak{P}/v)\, a(\mu_{\mathfrak{P}})$ is the induced level at $v$, the sum of the inertia degrees times the conductor exponents of the local components of $\mu$. The constant $\varepsilon$ is only asserted to exist and to be non-zero; no formula for it is claimed.
--
--   This is the place-by-place comparison step in the converse-theorem route to the Langlands–Tunnell theorem: it identifies the $\gamma$-factor datum $(R_1,R_2,m)$ of the cubic induction datum $X$ at the distinguished bad place $v$, assumed unramified in $K$, with the $\gamma$-factor built from the induced Euler polynomials of $\mu$ and $\mu^{-1}$ and the induced level, up to a single non-zero constant. It is used by [`LanglandsTunnell.CubicInduction.exists_localZeta31_fe_one_inducedEulerPoly_rational_of_isCubicInductionDataOn_of_not_isRamifiedIn`](thm.html#LanglandsTunnell.CubicInduction.exists_localZeta31_fe_one_inducedEulerPoly_rational_of_isCubicInductionDataOn_of_not_isRamifiedIn), from which the constant is subsequently eliminated.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_eval_mul_eq_mul_eval_of_forall_localZeta31_fe_one_of_isCubicInductionDataOn_of_addCharLevel.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal MeasureTheory LanglandsTunnell.RankinSelberg

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in
open scoped Classical in

theorem LanglandsTunnell.CubicInduction.exists_eval_mul_eq_mul_eval_of_forall_localZeta31_fe_one_of_isCubicInductionDataOn_of_addCharLevel
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hμ : IsAdmissibleTwist K μ)
    (_hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (_hns : ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSbad : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w ↔ w ∈ S)
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ
      (S : Set (HeightOneSpectrum (𝓞 ℚ))) X)
    (hcont : Continuous X.form) (hW : IsGaugeMajorised3 ℚ X.whittaker) (hW' : IsGaugeMajorised3 ℚ X.dualWhittaker)
    (hcontW : Continuous X.whittaker) (hcontW' : Continuous X.dualWhittaker)
    (c : ℂ) (hc : c * ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ)).toReal : ℂ) = 1)
    (hexp : X.form ≠ 0 ∧ ∀ v, ¬ IsBadPlace K μ v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
        X.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v (X.whittakerLoc v))
    (hbad : ∀ T : Finset (HeightOneSpectrum (𝓞 ℚ)),
      (∀ v ∈ T, IsBadPlace K μ v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
        ∀ k ∈ Uv, ∀ g : LocalGL3 v, X.whittakerLoc v (g * k) = X.whittakerLoc v g) ∧
      (∀ v ∈ T, IsBadPlace K μ v → ∀ W ∈ gl3CyclicSubspace (X.whittakerLoc v), W ≠ 0 →
        X.whittakerLoc v ∈ gl3CyclicSubspace W))
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ∈ S)
    (h1 : ∀ w ∈ S, w ≠ v → X.whittakerLoc w 1 = 1)
    (hadm : ∀ w ∈ S, ∀ Uw : Subgroup (LocalGL3 w), IsOpen (Uw : Set (LocalGL3 w)) →
      ∃ B : Finset (LocalGL3 w → ℂ), ∀ G ∈ gl3CyclicSubspace (X.whittakerLoc w),
        (∀ k ∈ Uw, ∀ g : LocalGL3 w, G (g * k) = G g) → G ∈ Submodule.span ℂ (B : Set (LocalGL3 w → ℂ)))
    (hcent : ∀ w ∈ S,
      (∀ z : (w.adicCompletion ℚ)ˣ, ‖((TateGlobal.localChar X.centralChar w z : ℂˣ) : ℂ)‖ = 1) ∧
      ∀ (t : (w.adicCompletion ℚ)ˣ) (h : LocalGL3 w),
        X.whittakerLoc w (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) =
          ((TateGlobal.localChar X.centralChar w t : ℂˣ) : ℂ) * X.whittakerLoc w h)
    (hψw : ∀ w ∈ S, LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ w) = 0)
    (hS : ∀ τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ τ → ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ∃ σ₀ : ℝ,
      ∀ s : ℂ, σ₀ < s.re →
        Integrable (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
          X.whittaker (iotaGL (diagUnitGL2 a) * g) * ((τ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1))
          (NumberField.Idele.productMeasureData ℚ S).νS)
    (hS' : ∀ τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ τ → ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ∃ σ₀ : ℝ,
      ∀ s : ℂ, σ₀ < s.re →
        Integrable (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
          (∫ y : mixedEmbedding.mixedSpace ℚ,
              dualWhittakerFn3 X.whittakerArch (archComponent3 (𝓞 ℚ) ℚ (iotaGL (diagUnitGL2 a)) *
                lowerUnipotent21 ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y) * archComponent3 (𝓞 ℚ) ℚ g)) *
            (∏ v ∈ S,
              (letI := LanglandsTunnell.TateLocal.localBorel ℚ v
               ((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set
                 (v.adicCompletion ℚ)) : ℂ)⁻¹ *
                 ∫ x : v.adicCompletion ℚ,
                   dualWhittakerFn3 (X.whittakerLoc v) (componentAt3 (𝓞 ℚ) ℚ v (iotaGL (diagUnitGL2 a)) *
                     lowerUnipotent21 x * componentAt3 (𝓞 ℚ) ℚ v g)
                     ∂(LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v))) *
            ((τ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1))
          (NumberField.Idele.productMeasureData ℚ S).νS)
    (hKv : ¬ IsRamifiedIn K v) (hψv : LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
    M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (harch : (∃ (gInf : GL (Fin 3) (InfiniteAdeleRing ℚ)) (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ), IsAdmissibleTwist ℚ σ ∧
      (∃ (t : ℂ) (e : ℤ), (∀ w : InfinitePlace ℚ, w.IsReal → IsArchCompAt ℚ σ w t e) ∧
        (((1 : (v.adicCompletion ℚ)ˣ →* ℂˣ) (-1) : ℂˣ) : ℂ) = (-1 : ℂ) ^ e) ∧
      ∀ σ₀ : ℝ, ∃ s : ℂ, σ₀ < s.re ∧ archZeta30 ν_mul (fun h => X.whittakerArch (h * gInf)) (σ.comp E) s 1 ≠ 0))
    (R₁ R₂ : Polynomial ℂ) (m : ℤ) (hR₁ : R₁ ≠ 0) (hR₂ : R₂ ≠ 0)
    (hFE1 :
        ∀ g : LocalGL3 v,
          letI := localBorel ℚ v
          ∃ (Q₁ Q₂ : Polynomial ℂ) (n : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
            IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (X.whittakerLoc
              v) 1 g σ₀ ∧
            (∀ s : ℂ, σ₀ < s.re →
              localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (X.whittakerLoc v) 1 s g *
                Q₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
              Q₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((n : ℂ) * s)) ∧
            IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt
              ℚ v) (dualWhittakerFn3 (X.whittakerLoc v)) 1⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
            (∀ s : ℂ, σ₁ < (1 - s).re →
              localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
                (X.whittakerLoc v) 1 (1 - s) g *
                (Q₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * R₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) =
              R₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * Q₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) *
                (Ideal.absNorm v.asIdeal : ℂ) ^ (((m : ℂ) + (n : ℂ)) * s))) :
    ∃ ε : ℂ, ε ≠ 0 ∧ ∀ s : ℂ,
      R₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s) *
          (inducedEulerPoly ℚ (inducedCoeff K μ⁻¹) v).eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))) =
        ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((inducedLevelAt K μ v : ℂ) * (1 / 2 - s)) *
          (inducedEulerPoly ℚ (inducedCoeff K μ) v).eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) *
          R₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by sorry
