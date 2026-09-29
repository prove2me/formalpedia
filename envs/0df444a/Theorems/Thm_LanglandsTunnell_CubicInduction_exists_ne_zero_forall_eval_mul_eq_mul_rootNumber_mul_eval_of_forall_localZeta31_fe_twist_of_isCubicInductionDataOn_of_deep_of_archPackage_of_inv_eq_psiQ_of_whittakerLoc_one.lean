-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_ne_zero_forall_eval_mul_eq_mul_rootNumber_mul_eval_of_forall_localZeta31_fe_twist_of_isCubicInductionDataOn_of_deep_of_archPackage_of_inv_eq_psiQ_of_whittakerLoc_one
-- name    : LanglandsTunnell.CubicInduction.exists_ne_zero_forall_eval_mul_eq_mul_rootNumber_mul_eval_of_forall_localZeta31_fe_twist_of_isCubicInductionDataOn_of_deep_of_archPackage_of_inv_eq_psiQ_of_whittakerLoc_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/c7c8ec26-a02d-5ce7-b309-83f87463bc56
-- title:
--   A twist-independent constant in the deep-place GL₃× GL₁ functional equation
-- statement:
--   Throughout, $K$ is a number field of degree $3$ over $\mathbb{Q}$, equipped with an algebra structure of $\mathcal{O}_{\mathbb{Q}}$ on $\mathcal{O}_K$ that is integral; $\psi$ is an additive character of the adele ring of $\mathbb{Q}$ which is `IsGlobalAddChar`, i.e. trivial on principal adeles, continuous and non-trivial; and $\mu$ is a character of the ideles of $K$ which is an admissible twist, i.e. trivial on $K^\times$, continuous and of absolute value $1$. Two further conditions are imposed on these data: at every finite place of $\mathbb{Q}$ that is not bad for $(K,\mu)$ — bad meaning that some prime of $K$ above it is ramified or that $\mu$ is ramified at some prime above it — the local component `psiLoc` of $\psi$ has `addCharLevel` equal to $0$ (hypothesis `_hlev`); and $\mu$ is not of base-change shape over $\mathbb{Q}$ in the following sense (hypothesis `_hns`): there is no admissible twist $\eta$ of $\mathbb{Q}$ such that, for every prime $\mathfrak{P}$ of $K$ at which $\mu$ is unramified and with $\eta$ unramified at the prime below, $\mu$ of the uniformiser idele at $\mathfrak{P}$ equals $\eta$ of the uniformiser idele below, raised to the inertia degree.
--
--   The measure-theoretic frame on $GL_2$ over $\mathbb{Q}$ is the `productionPinsOf` package built from a set $D$ of adelic $GL_2$, a family $U$ of level subgroups indexed by ideals, a family `gen` of Hecke generators, and the adelic box: Borel structures, the adelic $GL$ Haar measure, full central subgroup, and the additive measure given by conditioning adelic Haar on the box. The finite set $S$ of finite places of $\mathbb{Q}$ is required to consist exactly of the bad places (`hSbad`).
--
--   The central object is a tuple $X$ of type `CubicInductionData`, consisting of a global function `X.form` on adelic $GL_3$, its global Whittaker function `X.whittaker`, local Whittaker functions `X.whittakerLoc v` on $GL_3(\mathbb{Q}_v)$ for each finite $v$, an archimedean Whittaker function `X.whittakerArch`, a central character `X.centralChar`, and a dual Whittaker function `X.dualWhittaker`. The hypothesis `hX` asserts `IsCubicInductionDataOn K (productionPinsOf …) ψ μ S X`, a structure with twenty-three clauses, summarised here: automorphy of `X.form` under $GL_3(\mathbb{Q})$ and its transformation by the ideles-class central character `X.centralChar`; cuspidality of `X.form` along the two radicals $P_{21}$ and $P_{12}$; the identification of `X.whittaker` with the triple unipotent integral `whittaker3` against $\psi$, its $\psi$-Whittaker law, and the mirabolic expansion summing `X.whittaker` back to `X.form`; the $\psi_v$-Whittaker law of each `X.whittakerLoc v` and the factorisation of `X.whittaker` as `X.whittakerArch` at the archimedean component times the finite product of the local Whittaker values over any finite set containing $S$ outside which the components are integral; at places off $S$, `IsInducedSphericalAt` for the induced coefficients of $\mu$ (right invariance under the maximal compact, the two Hecke coset eigenvalue equations with eigenvalues $N_v\cdot e_1$, $N_v \cdot e_2$ of the induced Euler polynomial, and the central law with $e_3$), together with invariance under the congruence subgroup $K_1$ of the induced level at unramified places; Whittaker multiplicity one at every place; moderate growth of `X.form`, $K$-finiteness of `X.whittakerArch`, the iota-moment and Whittaker half-plane integrability conditions; and the corresponding dual clauses for `X.dualWhittaker` relative to $\psi^{-1}$ and the transpose-inverse form of `X.form`.
--
--   Further hypotheses on $X$: continuity of `X.form`, `X.whittaker` and `X.dualWhittaker`, and gauge majorisation `IsGaugeMajorised3` of the latter two (vanishing outside a root level and decay in the root-size gauge); a constant $c$ inverse to the adelic Haar volume of the adelic box; `hexp`, asserting $X.\mathrm{form}\neq 0$ and, at every non-bad $v$ with $\psi_v$ of level $0$, that `X.whittakerLoc v` takes the value $1$ at the identity and has the prescribed spherical torus values for the induced coefficients of $\mu$; `hbad`, asserting for every finite set $T$ of places that at each bad $v\in T$ the function `X.whittakerLoc v` is right invariant under some open subgroup and that every non-zero element $W$ of its cyclic subspace under right translation generates `X.whittakerLoc v` in turn; the normalisations `X.whittakerLoc w 1 = 1` at all $w \in S$ (separately for $w \neq v$ and for the distinguished place $v$); the admissibility condition `hadm`, that for each $w\in S$ and each open subgroup the invariants in the cyclic subspace of `X.whittakerLoc w` lie in the span of a finite set; the central condition `hcent`, that at each $w\in S$ the local component of `X.centralChar` is unitary and governs the transformation of `X.whittakerLoc w` under central scalars; and $\psi_w$ of level $0$ at all $w\in S$ and at $v$.
--
--   The two integrability premises `hS` and `hS'` require, for every admissible twist $\tau$ of $\mathbb{Q}$ and every $g$ in adelic $GL_3$, the existence of a half-plane on which the $S$-part measure `(productMeasureData ℚ S).νS` integrates, respectively, $a \mapsto X.\mathrm{whittaker}(\iota(\mathrm{diag}(a,1))g)\,\tau(a)\,\|a\|^{s-1}$ and the corresponding product of the archimedean and local mirabolic integrals of the dual Whittaker functions against the normalised self-dual Haar measures at the places of $S$.
--
--   Archimedean data: a homomorphism $E$ splitting the units of the infinite adeles into ideles with trivial finite part; a Haar measure $\nu_{\mathrm{mul}}$ on the units of the infinite adeles; families $u_R, a_R$ (valued in $\mathbb{C}$ and $\mathbb{Z}/2$) at the real places of $K$ and $u_C, k_C$ at the complex places, which are the archimedean exponents of $\mu$ in the sense of `IsArchCompAt`; the normalisation $\psi^{-1} =$ `psiQ`, the standard additive character of $\mathbb{Q}$; an admissible twist $\omega_3$ of $\mathbb{Q}$ which at every non-bad prime $p$ is unramified with Euler coefficient the third induced coefficient $e_3$ of $\mu$ at $p$, and whose archimedean exponent at each real place of $\mathbb{Q}$ is, for any families of archimedean exponents of $\mu$, the sum $\sum u_R + \sum 2u_C$ with parity exponent $\sum a_R + \sum (k_C+1)$; a non-zero rational $a$, a unit $a_\infty$ of the infinite adeles equal to the image of $a$, the archimedean character $x \mapsto \mathrm{psiArch}(ax)$ which is the restriction of $\psi$ to the infinite adeles, and the additive measure $\nu_{\mathrm{add}} = |a|^{1/2}$ times the transport of Lebesgue measure from the mixed space.
--
--   The archimedean Whittaker package `hWarch` concerns a function `Warch` on $GL_3$ of the infinite adeles and has seven clauses: `Warch` is non-zero and $K$-finite; it is continuous and satisfies a bound $C/((\prod_w \mathrm{archRoot}_1 \mathrm{archRoot}_2)^t (1+\mathrm{archRootSum})^N)$ for some $t$ and all $N$; it is a $\psi_\infty$-Whittaker function; it transforms under central scalars by $\omega_3 \circ E$; for every admissible twist $\sigma$ of $\mathbb{Q}$ with archimedean exponents $(t,e)$ at the real places and every $g_\infty$ there is an entire function $P$ such that `archZeta30` of $h \mapsto \mathrm{Warch}(h g_\infty)$ against $\sigma\circ E$ converges in a half-plane and equals $P(s)$ times the archimedean factor of the $L$-datum `heckeDatum K μ (uR + t) (aR + e) (uC + t) kC`, such that $P$ is bounded by $C\exp(A|\mathrm{Im}\,s|)$ in vertical strips, such that the product $P \cdot \mathrm{archFactor}$ decays faster than any power of $|\mathrm{Im}\,s|$ in vertical strips, and such that the dual archimedean zeta integral `archZetaDual31` at $1-s$ converges and equals the product of the sign constants $\prod_{w \text{ real}} \mathrm{signEpsilon}(a_R(w)+e)$, $\prod_{w \text{ complex}} i^{|k_C(w)|}$ and $\prod_{w} \mathrm{lambdaArch}\,K\,w$, times $\omega_3(E a_\infty)\sigma(E a_\infty)^3$, times $|a|^{3(s-1/2)}$, times $P(s)$ times the dual archimedean factor of the same $L$-datum at $1-s$; and finally there is an admissible twist $\sigma$ and a point $s$ at which `archZeta30` of `Warch` against $\sigma \circ E$ is non-zero. The last hypothesis is $X.\mathrm{whittakerArch} = \mathrm{Warch}$.
--
--   Under these hypotheses, and for a fixed place $v \in S$, the conclusion asserts the existence of a complex number $\mathrm{lam} \neq 0$ with the following property. Let $\eta$ be a character of $\mathbb{Q}_v^\times$ with conductor exponent $c_\eta$ in the sense of `HasConductorExponentAt`, and let $b$ be a natural number with $c_\eta \le b$, such that $v$ is deep for $\mu$ relative to $b$: for every prime $w$ of $K$ above $v$, $2\,e(w|v)\,b + 1 \le$ the conductor exponent of the local component of $\mu$ at $w$. Let $\eta_{\mathbb{A}}$ be an admissible twist of $\mathbb{Q}$ whose local component at $v$ is $\eta$ and whose composite with the idelic norm of the genuine base change from $\mathbb{Q}$ to $K$ is an admissible twist of $K$. Let $\ell$ be a natural number whose value as an integer is $\sum_{w \mid v} f(w|v)\,\mathrm{pinnedExp}\,K\,(\eta_{\mathbb{A}}\circ N \cdot \mu)\,w$, the finite sum over the fibre of $v$ of the inertia degrees times the pinned exponents, where the pinned exponent at $w$ is the conductor exponent of the local character plus the level of the standard local additive character at $w$.
--
--   Assume the archimedean non-vanishing datum: there are $g_\infty$ in $GL_3$ of the infinite adeles and an admissible twist $\sigma$ of $\mathbb{Q}$ admitting archimedean exponents $(t,e)$ at all real places of $\mathbb{Q}$ with $\eta(-1) = (-1)^e$, such that for every $\sigma_0$ there is $s$ with $\mathrm{Re}\,s > \sigma_0$ and `archZeta30` of $h \mapsto X.\mathrm{whittakerArch}(h g_\infty)$ against $\sigma \circ E$ non-zero at $s$.
--
--   Finally, let $R_1, R_2$ be non-zero polynomials over $\mathbb{C}$ and $m$ an integer forming a rational functional-equation datum for the local component of $X$ at $v$ twisted by $\eta$: for every $g \in GL_3(\mathbb{Q}_v)$ there are polynomials $Q_1, Q_2$ with $Q_2 \ne 0$, an integer $n$ and reals $\sigma_0, \sigma_1$ such that the zeta integral `localZeta30` of `X.whittakerLoc v` against $\eta$ converges for $\mathrm{Re}\,s > \sigma_0$ and satisfies there
--   $$\mathrm{localZeta30}(s,g)\,Q_2(N_v^{-s}) = Q_1(N_v^{-s})\,N_v^{ns},$$
--   and the dual integral converges — that is, `IsLocalZeta31ConvergentAbove` holds for $\mathrm{dualWhittakerFn3}$ of `X.whittakerLoc v` against $\eta^{-1}$ at $w' \cdot {}^t g^{-1}$ above $\sigma_1$ — and satisfies for $\sigma_1 < \mathrm{Re}(1-s)$
--   $$\mathrm{localZetaDual31}(1-s,g)\,Q_2(N_v^{-s})R_2(N_v^{-s}) = R_1(N_v^{-s})\,Q_1(N_v^{-s})\,N_v^{(m+n)s},$$
--   all integrals being taken with respect to the multiplicative measure obtained from the self-dual additive Haar measure at $v$ by pulling back its modulus density along the unit inclusion, and with respect to that self-dual measure in the additive variable, with $N_v$ the absolute norm of $v$.
--
--   Then for every $s \in \mathbb{C}$,
--   $$R_1(N_v^{-s})\,N_v^{ms} = \mathrm{lam}\cdot\Big(\prod_{w \mid v}\big(\eta_{\mathbb{A}}\circ N \cdot \mu\big)_w(-1)\cdot\prod_{w\mid v}\mathrm{stdRootNumberAt}\,K\,w\,\big((\eta_{\mathbb{A}}\circ N\cdot\mu)_w\big)\Big)\cdot N_v^{\ell(1/2-s)}\cdot R_2(N_v^{-s}),$$
--   the products being finite products over the fibre of $v$ in $K$ of the values at $-1$ and of the standard local root numbers at $1/2$ of the local components of the character $(\eta_{\mathbb{A}}\circ N)\cdot\mu$. The constant $\mathrm{lam}$ is quantified before $\eta$, $b$, $\eta_{\mathbb{A}}$, $\ell$, $R_1$, $R_2$ and $m$, and so does not depend on them.
--
--   This is the comparison, at a place $v$ which is bad for $(K,\mu)$ and deep relative to the twist, between the local functional-equation factor of the $GL_3 \times GL_1$ zeta integrals of the cubic-induction Whittaker data and the product over the primes of $K$ above $v$ of the Tate local root numbers of the corresponding characters: the factor is a Tate monomial in $N_v^{-s}$ times one non-zero constant that is independent of the twisting character. It feeds the identification of the local constants in the converse-theorem input for Langlands–Tunnell, and is used by the two subsequent statements about the cyclic subspace at deep places and over the whole set of bad places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_ne_zero_forall_eval_mul_eq_mul_rootNumber_mul_eval_of_forall_localZeta31_fe_twist_of_isCubicInductionDataOn_of_deep_of_archPackage_of_inv_eq_psiQ_of_whittakerLoc_one.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_M4aHerbrand_GenuineDescent
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
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_HonestLDatum
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_LanglandsTunnell_LambdaSquared

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal MeasureTheory LanglandsTunnell.RankinSelberg
open NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion LanglandsTunnell.CubicLambda

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in
open scoped Classical in

theorem LanglandsTunnell.CubicInduction.exists_ne_zero_forall_eval_mul_eq_mul_rootNumber_mul_eval_of_forall_localZeta31_fe_twist_of_isCubicInductionDataOn_of_deep_of_archPackage_of_inv_eq_psiQ_of_whittakerLoc_one
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
    (hv1 : X.whittakerLoc v 1 = 1)
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
    (hψv : LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
    M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]

    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ)
    (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ)
    (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (hcR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (hcC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
    (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ)

    (ω₃ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω₃ : IsAdmissibleTwist ℚ ω₃ ∧
      (∀ p : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ p →
        IsUnramifiedCharAt ω₃ p ∧ eulerCoeff ℚ ω₃ p = inducedE3 ℚ (inducedCoeff K μ) p) ∧
      ∀ (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
        (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ),
        (∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ)) →
        (∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw)) →
        ∀ v : InfinitePlace ℚ, v.IsReal →
          IsArchCompAt ℚ ω₃ v
            ((∑ᶠ (w) (hw : w.IsReal), uR w hw) + (∑ᶠ (w) (hw : w.IsComplex), 2 * uC w hw))
            ((∑ᶠ (w) (hw : w.IsReal), ((aR w hw).val : ℤ)) + (∑ᶠ (w) (hw : w.IsComplex), (kC w hw + 1))))
    (a : ℚ) (ha : a ≠ 0) (aInf : (InfiniteAdeleRing ℚ)ˣ)
    (haInf : (aInf : InfiniteAdeleRing ℚ) = algebraMap ℚ (InfiniteAdeleRing ℚ) a)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (hψinf : ψ.compAddMonoidHom
        (AddMonoidHom.inl (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)) = psiInf)
    [mA : MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    (ν_add : MeasureTheory.Measure (InfiniteAdeleRing ℚ))
    (hν_add : ν_add = ENNReal.ofReal (|(a : ℝ)| ^ ((1 : ℝ) / 2)) •
      MeasureTheory.Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm MeasureTheory.volume)
    (Warch : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ)
    (hWarch :
      Warch ≠ 0 ∧ IsKFinite Warch ∧
      (Continuous Warch ∧ ∃ t : ℕ, ∀ N : ℕ, ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ‖Warch (archComponent3 (𝓞 ℚ) ℚ g)‖ ≤
        C / ((∏ w : InfinitePlace ℚ, archRoot₁ ℚ w g * archRoot₂ ℚ w g) ^ t * (1 + archRootSum ℚ g) ^ N)) ∧
      IsGL3PsiWhittakerFn psiInf Warch ∧
      (∀ (z : (InfiniteAdeleRing ℚ)ˣ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)),
        Warch (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((ω₃ (E z) : ℂˣ) : ℂ) * Warch g) ∧
      (∀ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ →
        ∀ (t : ℂ) (e : ℤ), (∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v t e) →
        ∀ gInf : GL (Fin 3) (InfiniteAdeleRing ℚ), ∃ P : ℂ → ℂ, Differentiable ℂ P ∧
          (∃ σ₀ : ℝ, IsArchZeta30ConvergentAbove ν_mul (fun h => Warch (h * gInf)) (σ.comp E) 1 σ₀ ∧
            ∀ s : ℂ, σ₀ < s.re →
              archZeta30 ν_mul (fun h => Warch (h * gInf)) (σ.comp E) s 1 =
                P s *
                  (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
                    (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactor s) ∧
          (∀ σ₁ σ₂ : ℝ, ∃ C A : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
            ‖P s‖ ≤ C * Real.exp (A * |s.im|)) ∧
          (∀ (σ₁ σ₂ : ℝ) (N : ℕ), ∃ C T₀ : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → T₀ ≤ |s.im| →
            |s.im| ^ N *
              ‖P s *
                (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
                  (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactor s‖ ≤ C) ∧
          (∃ σ₁ : ℝ, IsArchZeta31ConvergentAbove ν_mul ν_add (dualWhittakerFn3 (fun h => Warch (h * gInf)))
              (σ.comp E)⁻¹ (weylPrime3 * transposeInv3 1) σ₁ ∧
            ∀ s : ℂ, σ₁ < (1 - s).re →
              archZetaDual31 ν_mul ν_add (fun h => Warch (h * gInf)) (σ.comp E) (1 - s) 1 =
                (((Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).prod
                    fun w => signEpsilon (aR w.1 w.2 + (e : ZMod 2))) *
                  ((Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).prod
                      fun w => Complex.I ^ (kC w.1 w.2).natAbs) *
                  ∏ w : InfinitePlace K, lambdaArch K w) *
                (((ω₃ (E aInf) : ℂˣ) : ℂ) * ((σ (E aInf) : ℂˣ) : ℂ) ^ 3) *
                (((|a| : ℝ) : ℂ) ^ (3 * (s - 1 / 2))) *
                P s *
                  (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
                    (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactorDual (1 - s))) ∧
      ∃ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ ∧
        ∃ s : ℂ, archZeta30 ν_mul Warch (σ.comp E) s 1 ≠ 0)
    (hArchEq : X.whittakerArch = Warch)
    :
    ∃ lam : ℂ, lam ≠ 0 ∧
      ∀ (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (cη b : ℕ), LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v η cη → cη ≤ b →
        (∀ w ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ K v,
          2 * (Ideal.ramificationIdx' (w.under (𝓞 ℚ)).asIdeal w.asIdeal * b) + 1 ≤
            LanglandsTunnell.TateLocal.conductorExponentAt K w (NumberField.TateGlobal.localChar μ w)) →
        ∀ ηA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, LanglandsTunnell.Converse.IsAdmissibleTwist ℚ ηA →
          NumberField.TateGlobal.localChar ηA v = η →
          LanglandsTunnell.Converse.IsAdmissibleTwist K (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) →
        ∀ ℓ : ℕ, ((ℓ : ℤ) = ∑ᶠ w ∈ primeFibre ℚ K v, (v.asIdeal.inertiaDeg' w.asIdeal : ℤ) *
          LanglandsTunnell.Converse.pinnedExp K (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w) →

        (∃ (gInf : GL (Fin 3) (InfiniteAdeleRing ℚ)) (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ), IsAdmissibleTwist ℚ σ ∧
          (∃ (t : ℂ) (e : ℤ), (∀ w : InfinitePlace ℚ, w.IsReal → IsArchCompAt ℚ σ w t e) ∧
            ((η (-1) : ℂˣ) : ℂ) = (-1 : ℂ) ^ e) ∧
          ∀ σ₀ : ℝ, ∃ s : ℂ, σ₀ < s.re ∧ archZeta30 ν_mul (fun h => X.whittakerArch (h * gInf)) (σ.comp E) s 1 ≠ 0) →
        ∀ (R₁ R₂ : Polynomial ℂ) (m : ℤ), R₁ ≠ 0 → R₂ ≠ 0 →
          (∀ g : LocalGL3 v,
            letI := localBorel ℚ v
            ∃ (Q₁ Q₂ : Polynomial ℂ) (n : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
              IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (X.whittakerLoc
                v) η g σ₀ ∧
              (∀ s : ℂ, σ₀ < s.re →
                localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (X.whittakerLoc v) η s g *
                  Q₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
                Q₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((n : ℂ) * s)) ∧
              IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt
                ℚ v) (dualWhittakerFn3 (X.whittakerLoc v)) η⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
              (∀ s : ℂ, σ₁ < (1 - s).re →
                localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
                  (X.whittakerLoc v) η (1 - s) g *
                  (Q₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * R₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) =
                R₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * Q₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) *
                  (Ideal.absNorm v.asIdeal : ℂ) ^ (((m : ℂ) + (n : ℂ)) * s))) →
        ∀ s : ℂ,
          R₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s) =
            lam * ((∏ᶠ w ∈ primeFibre ℚ K v,
                ((NumberField.TateGlobal.localChar
                  (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w (-1) : ℂˣ) : ℂ)) *
              ∏ᶠ w ∈ primeFibre ℚ K v,
                LanglandsTunnell.TateLocal.stdRootNumberAt K w
                  (NumberField.TateGlobal.localChar
                    (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w)) *
            (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s)) * R₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by sorry
