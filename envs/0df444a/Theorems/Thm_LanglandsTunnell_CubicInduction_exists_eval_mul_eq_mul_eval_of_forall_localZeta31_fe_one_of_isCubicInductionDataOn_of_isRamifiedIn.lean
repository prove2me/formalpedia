-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_eval_mul_eq_mul_eval_of_forall_localZeta31_fe_one_of_isCubicInductionDataOn_of_isRamifiedIn
-- name    : LanglandsTunnell.CubicInduction.exists_eval_mul_eq_mul_eval_of_forall_localZeta31_fe_one_of_isCubicInductionDataOn_of_isRamifiedIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/66ea86ac-a3e8-552d-a6cb-552780a7d47e
-- title:
--   Ramified place: local functional-equation datum matches induced Euler polynomials
-- statement:
--   Throughout, $K$ is a number field of degree $3$ over $\mathbb{Q}$ whose ring of integers is an integral $\mathcal{O}_{\mathbb{Q}}$-algebra, $\psi$ is an additive character of the adele ring of $\mathbb{Q}$ with values in $\mathbb{C}$, and $\mu$ is a homomorphism from the idele units of $K$ to $\mathbb{C}^{\times}$. For a finite place $v$ of $\mathbb{Q}$, $N_v$ denotes the absolute norm of the prime ideal of $v$, $\psi_v =$ `psiLoc` $\psi\,v$ is the composite of $\psi$ with the inclusion of the completion at $v$ into the adeles, and `LocalGL3 v` is $\mathrm{GL}_3$ of that completion.
--
--   Global hypotheses. `_hdeg` states that the $\mathbb{Q}$-rank of $K$ is $3$; `_hψ` states that $\psi$ is a global additive character, i.e. trivial on principal adeles, continuous and not identically $1$; `_hμ` states that $\mu$ is an admissible twist of $K$, i.e. trivial on the principal ideles, continuous and of absolute value $1$ at every idele. The hypothesis `_hlev` requires $\psi_v$ to have level $0$ (the supremum of those $n$ with $\psi_v$ trivial on the valuation ideal $\mathrm{exp}(n)$ being $0$) at every finite place $v$ of $\mathbb{Q}$ that is not a bad place for $(K,\mu)$, a bad place being one which is ramified in $K$ or above which $\mu$ is twist-ramified. The non-descent hypothesis `_hns` asserts that there is no admissible twist $\eta$ of the ideles of $\mathbb{Q}$ such that for every prime $\mathfrak{P}$ of $\mathcal{O}_K$ at which $\mu$ is unramified and with $\eta$ unramified at the prime $\mathfrak{p}$ of $\mathbb{Q}$ below $\mathfrak{P}$, the value of $\mu$ at the uniformizer idele of $\mathfrak{P}$ equals the value of $\eta$ at the uniformizer idele of $\mathfrak{p}$ raised to the inertia degree of $\mathfrak{P}$ over $\mathfrak{p}$.
--
--   Carrier and Whittaker data. A set $D$ in the adelic $\mathrm{GL}_2$ of $\mathbb{Q}$, a family $U$ of subgroups indexed by the ideals of $\mathcal{O}_{\mathbb{Q}}$ and a family $\mathrm{gen}$ of adelic $\mathrm{GL}_2$ elements indexed by the finite places are assembled into the carrier pins `productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)`, whose measures are the adelic Haar measures, whose central subgroup is the whole idele group and whose adelic measure is the Haar measure conditioned on the adelic box. A finite set $S$ of finite places of $\mathbb{Q}$ is required by `hSbad` to consist exactly of the bad places of $(K,\mu)$. The datum $X$ consists of a function `form` on the adelic $\mathrm{GL}_3$ of $\mathbb{Q}$, a global Whittaker function `whittaker`, local Whittaker functions `whittakerLoc v` on `LocalGL3 v`, an archimedean Whittaker function `whittakerArch`, a central character `centralChar` on the ideles and a dual Whittaker function `dualWhittaker`. The hypothesis `hX` asserts `IsCubicInductionDataOn` for $K$, these pins, $\psi$, $\mu$ and $S$: its clauses (summarised here) require left invariance of `form` under the rational points, the central transformation law with character `centralChar` which is trivial on principal ideles, cuspidality along both maximal parabolics, the identification of `whittaker` with the $\psi$-Whittaker integral of `form` together with the $\psi$-Whittaker transformation law and the mirabolic Fourier expansion summing to `form`, the $\psi_v$-Whittaker law for each `whittakerLoc v`, factorisation of `whittaker` as `whittakerArch` at the archimedean component times the finite product of the `whittakerLoc v` over any finite set containing $S$ outside which the components lie in the maximal compact, sphericity off $S$ of induced type with Hecke eigenvalues built from the coefficients `inducedCoeff K μ`, right invariance off $S$ under the congruence subgroup attached to the induced level at places unramified in $K$, local Whittaker multiplicity one, moderate growth of `form`, $K$-finiteness of `whittakerArch`, the iota-moment and Whittaker half-plane conditions, and the corresponding statements for `dualWhittaker` as the $\psi^{-1}$-Whittaker integral of the dual form.
--
--   Regularity and normalisation. `hcont` asserts continuity of `X.form`; `hW` and `hW'` assert that `X.whittaker` and `X.dualWhittaker` are gauge-majorised on the adelic $\mathrm{GL}_3$ of $\mathbb{Q}$ (supported in a root level and bounded there by the prescribed gauge quotients); `hcontW` and `hcontW'` assert their continuity. A complex number $c$ is given with `hc`: $c$ times the adelic Haar volume of the adelic box of $\mathbb{Q}$ equals $1$.
--
--   Normalisation off $S$ and local conditions on $S$. `hexp` asserts that `X.form` is not identically zero and that at every place $v$ that is not bad and at which $\psi_v$ has level $0$ one has $(X.\mathrm{whittakerLoc}\,v)(1)=1$ and `HasSphericalTorusValuesAt (inducedCoeff K μ) v (X.whittakerLoc v)`, i.e. the explicit spherical values on the torus points and on the two-row points attached to the induced Satake parameters. `hbad` asserts, for every finite set $T$ of places, two clauses for the bad places $v \in T$: first, that `X.whittakerLoc v` is right invariant under some open subgroup of `LocalGL3 v`; second, that `X.whittakerLoc v` lies in the cyclic subspace generated by the right translates of any non-zero member of its own cyclic subspace. A place $v \in S$ is fixed (`hv`). The hypothesis `h1` requires $(X.\mathrm{whittakerLoc}\,w)(1)=1$ for every $w \in S$ with $w \neq v$; `hadm` requires, for each $w \in S$ and each open subgroup $U_w$ of `LocalGL3 w`, a finite set $B$ of functions whose complex span contains every $U_w$-right-invariant element of the cyclic subspace of `X.whittakerLoc w`; `hcent` requires, for each $w \in S$, that the local component of `X.centralChar` at $w$ has absolute value $1$ and that `X.whittakerLoc w` transforms by that local character under scalar matrices; `hψw` requires $\psi_w$ to have level $0$ for every $w \in S$.
--
--   Global integrability. `hS` asserts that for every admissible twist $\tau$ of the ideles of $\mathbb{Q}$ and every $g$ in the adelic $\mathrm{GL}_3$ there is $\sigma_0$ such that for $\mathrm{Re}\,s > \sigma_0$ the function $a \mapsto X.\mathrm{whittaker}(\iota(\mathrm{diag}(a,1))\,g)\,\tau(a)\,\|a\|^{s-1}$ is integrable for the $S$-part measure of [`NumberField.Idele.productMeasureData ℚ S`](def/NumberField_IdeleProductMeasure.html#L679). `hS'` asserts the analogous integrability for the dual integrand, in which $X.\mathrm{whittaker}$ is replaced by the product of the integral over the mixed space of $\mathbb{Q}$ of `dualWhittakerFn3 X.whittakerArch` along the lower unipotent one-parameter subgroup, twisted by the archimedean components of $\iota(\mathrm{diag}(a,1))$ and of $g$, with the product over $v \in S$ of the corresponding local integrals of `dualWhittakerFn3 (X.whittakerLoc v)` against the self-dual Haar measure at $v$, each normalised by the inverse of the measure of the local integers.
--
--   The place $v$, the exponent $\ell$ and archimedean data. `hKv` asserts that $v$ is ramified in $K$, i.e. some prime of $\mathcal{O}_K$ above $v$ has ramification index different from $1$. A natural number $\ell$ is given with `hℓ`: its integer image is the finite sum over the primes $w$ of $\mathcal{O}_K$ above $v$ of the inertia degree of $w$ over $v$ times `pinnedExp K μ w`, the latter being the conductor exponent at $w$ of the local component of $\mu$ plus the level of the standard additive character of $K$ at $w$. `hψv` requires $\psi_v$ to have level $0$. A monoid homomorphism $E$ from the units of the infinite adele ring of $\mathbb{Q}$ to the idele units is given with `hE`: the infinite part of $E(u)$ is $u$ and its finite part is $1$. The units of the infinite adele ring carry a measurable structure which is the Borel structure, and $\nu_{\mathrm{mul}}$ is a Haar measure on them. The hypothesis `harch` asserts the existence of $g_\infty \in \mathrm{GL}_3$ of the infinite adele ring and of an admissible twist $\sigma$ of the ideles of $\mathbb{Q}$ such that: there are $t \in \mathbb{C}$ and $e \in \mathbb{Z}$ with `IsArchCompAt ℚ σ w t e` at every real infinite place $w$ of $\mathbb{Q}$ (the archimedean local component of $\sigma$ being the norm to the power $\mathrm{mult}(w)\,t$ times the $e$-th power of the normalised embedding) and with the value at $-1$ of the trivial character of the units of the completion at $v$ equal to $(-1)^{e}$; and for every $\sigma_0$ there is $s$ with $\mathrm{Re}\,s > \sigma_0$ at which the archimedean zeta integral `archZeta30` of $\nu_{\mathrm{mul}}$, the function $h \mapsto X.\mathrm{whittakerArch}(h\,g_\infty)$, the character $\sigma \circ E$, the variable $s$ and the identity matrix is non-zero.
--
--   The rational local functional-equation datum at $v$. Non-zero polynomials $R_1, R_2 \in \mathbb{C}[X]$ and an integer $m$ are given (`hR₁`, `hR₂`). The hypothesis `hFE1` asserts that for every $g \in$ `LocalGL3 v` there exist polynomials $Q_1, Q_2$ with $Q_2 \neq 0$, an integer $n$ and reals $\sigma_0, \sigma_1$ such that, with respect to the multiplicative measure obtained from the self-dual Haar measure at $v$ and the trivial character: the zeta integral `localZeta30` of `X.whittakerLoc v` at $g$ converges for $\mathrm{Re}\,s > \sigma_0$ and satisfies there
--   $$\mathrm{localZeta30}(s,g)\;Q_2(N_v^{-s}) \;=\; Q_1(N_v^{-s})\,N_v^{\,n s};$$
--   the integral `localZeta31` of `dualWhittakerFn3 (X.whittakerLoc v)` with the inverse of the trivial character at `weylPrime3 * transposeInv3 g` converges for $\mathrm{Re}\,s > \sigma_1$; and for all $s$ with $\sigma_1 < \mathrm{Re}(1-s)$,
--   $$\mathrm{localZetaDual31}(1-s,g)\;\bigl(Q_2(N_v^{-s})\,R_2(N_v^{-s})\bigr) \;=\; R_1(N_v^{-s})\,Q_1(N_v^{-s})\,N_v^{\,(m+n)s},$$
--   where `localZetaDual31` is `localZeta31` of the dual Whittaker function at `weylPrime3 * transposeInv3 g` with the inverted character.
--
--   Conclusion. There exists $\varepsilon \in \mathbb{C}$ with $\varepsilon \neq 0$ such that for every $s \in \mathbb{C}$
--   $$R_1(N_v^{-s})\,N_v^{\,m s}\;E^{\vee}\bigl(N_v^{-(1-s)}\bigr) \;=\; \varepsilon\,N_v^{\,\ell(1/2-s)}\;E\bigl(N_v^{-s}\bigr)\,R_2(N_v^{-s}),$$
--   where $E$ is the induced Euler polynomial `inducedEulerPoly ℚ (inducedCoeff K μ) v` and $E^{\vee}$ is `inducedEulerPoly ℚ (inducedCoeff K μ⁻¹) v`, each being the finite product over the primes of $\mathcal{O}_K$ above $v$ of the local factors attached to the coefficients `inducedCoeff` of $\mu$, respectively of $\mu^{-1}$.
--
--   This is the local–global compatibility at a place of $\mathbb{Q}$ ramified in the cubic field $K$: a rational functional-equation datum for the local Whittaker function of the cubic-induction data at $v$ is forced to agree, up to a non-zero constant and the power $N_v^{\ell(1/2-s)}$, with the ratio of the induced Euler polynomials of $\mu$ and $\mu^{-1}$ at $v$. It is used by `exists_localZeta31_fe_one_inducedEulerPoly_rational_of_isCubicInductionDataOn_of_isRamifiedIn` in the converse-theorem construction of the automorphic induction of $\mu$ from $K$ to $\mathrm{GL}_3(\mathbb{Q})$, which underlies the Langlands–Tunnell theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_eval_mul_eq_mul_eval_of_forall_localZeta31_fe_one_of_isCubicInductionDataOn_of_isRamifiedIn.lean

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

theorem LanglandsTunnell.CubicInduction.exists_eval_mul_eq_mul_eval_of_forall_localZeta31_fe_one_of_isCubicInductionDataOn_of_isRamifiedIn
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
    (hKv : IsRamifiedIn K v)
    (ℓ : ℕ) (hℓ : (ℓ : ℤ) = ∑ᶠ w ∈ primeFibre ℚ K v, (v.asIdeal.inertiaDeg' w.asIdeal : ℤ) * LanglandsTunnell.Converse.pinnedExp K μ w) (hψv : LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
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
        ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s)) *
          (inducedEulerPoly ℚ (inducedCoeff K μ) v).eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) *
          R₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by sorry
