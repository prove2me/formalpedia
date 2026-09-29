-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_finprod_sq_mul_lamSqArch_eq_one_of_forall_ne_zero_localZeta31_fe_rootNumber_of_isCubicInductionDataOn_of_archPackage_of_inv_eq_psiQ
-- name    : LanglandsTunnell.CubicInduction.finprod_sq_mul_lamSqArch_eq_one_of_forall_ne_zero_localZeta31_fe_rootNumber_of_isCubicInductionDataOn_of_archPackage_of_inv_eq_psiQ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/3416be83-7559-5e9b-98b9-4fde93305cae
-- title:
--   Product formula (prodᵥλᵥ²) λ_∞²=1 for a cubic induction
-- statement:
--   Setting. Let $K$ be a number field of degree $3$ over $\mathbb{Q}$ (the hypothesis `_hdeg` asserts $\operatorname{finrank}_{\mathbb{Q}}K=3$), with $\mathcal{O}_K$ an integral $\mathcal{O}_{\mathbb{Q}}$-algebra. Let $\psi$ be an additive character of the adele ring of $\mathbb{Q}$ which is a global additive character in the sense of `IsGlobalAddChar` (`_hψ`: trivial on the principal adeles, continuous, and non-trivial), and let $\mu$ be a homomorphism from the ideles of $K$ to $\mathbb{C}^\times$ which is an admissible twist (`_hμ`: trivial on principal ideles, continuous, unitary). The hypothesis `_hlev` states that the local component `psiLoc ψ v` has `addCharLevel` equal to $0$ at every finite place $v$ of $\mathbb{Q}$ which is not a bad place for $(K,\mu)$, a bad place being one that is ramified in $K$ or below a prime at which $\mu$ is ramified. The hypothesis `_hns` asserts that $\mu$ is not of base-change shape: there is no admissible twist $\eta$ of $\mathbb{Q}$ such that for every prime $\mathfrak{P}$ of $K$ at which $\mu$ is unramified and whose prime $p$ below is unramified for $\eta$ one has $\mu(\varpi_{\mathfrak{P}})=\eta(\varpi_p)^{f(\mathfrak{P}/p)}$, with $\varpi$ the uniformiser ideles and $f$ the inertia degree.
--
--   Carrier and data. Let $D$ be a subset of the adelic $GL_2$ over $\mathbb{Q}$, $U$ an assignment of subgroups of that group to ideals of $\mathcal{O}_{\mathbb{Q}}$, and `gen` an assignment of elements to finite places; these enter through `productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)`, the carrier pins whose measurable structures are the Borel ones, whose $GL_2$-measure is the adelic Haar measure, whose central subgroup is the whole idele group, and whose additive measure is adelic Haar conditioned on the adelic box. Let $S$ be a finite set of finite places of $\mathbb{Q}$ which, by `hSbad`, consists exactly of the bad places for $(K,\mu)$. Let $X$ be a `CubicInductionData`, i.e. a tuple consisting of a function `form` on adelic $GL_3$, global Whittaker and dual Whittaker functions, local Whittaker functions `whittakerLoc v` on $GL_3(\mathbb{Q}_v)$, an archimedean Whittaker function `whittakerArch`, and a central character. The hypothesis `hX` asserts `IsCubicInductionDataOn` for $K$, the above pins, $\psi$, $\mu$ and $S$ (twenty clauses, summarised here): left invariance of `form` under $GL_3(\mathbb{Q})$, transformation of `form` under the central scalars by `centralChar`, triviality of `centralChar` on principal ideles, cuspidality of `form` along the radicals of the two maximal parabolics, the identification of `whittaker` with the triple $\psi$-Fourier integral `whittaker3` of `form` and the $\psi$-Whittaker law for it, the mirabolic Fourier expansion summing `whittaker` to `form`, the $\psi_v$-Whittaker laws for the `whittakerLoc v`, factorisability of `whittaker` as `whittakerArch` on the archimedean component times the finite local factors over any finite set containing $S$ outside which the component is integral, sphericality off $S$ with Hecke eigenvalues given by the induced data `inducedE1`, `inducedE2`, `inducedE3` of `inducedCoeff K μ`, invariance under `congruenceK1` of level `inducedLevelAt K μ v` at unramified places off $S$, the Whittaker multiplicity-one property locally, moderate growth of `form`, $K$-finiteness of `whittakerArch`, the iota-moment and Whittaker half-plane integrability conditions, and the corresponding clauses for `dualWhittaker` relative to $\psi^{-1}$ and the transpose-inverse form.
--
--   Regularity and normalisation. The hypotheses `hcont`, `hcontW`, `hcontW'` give continuity of `form`, `whittaker` and `dualWhittaker`; `hW`, `hW'` give the gauge majorisation `IsGaugeMajorised3` of `whittaker` and `dualWhittaker` (vanishing outside a root level, and rapid decay in terms of `rootSizeProd` and `archRootSum`); `hc` provides a scalar $c$ inverse to the volume of the adelic box.
--
--   Local hypotheses at good and bad places. The hypothesis `hexp` asserts that `form` is non-zero and that at every place $v$ which is not bad and at which `psiLoc ψ v` has level $0$ one has `X.whittakerLoc v 1 = 1` together with `HasSphericalTorusValuesAt (inducedCoeff K μ) v`, i.e. the prescribed values of the local Whittaker function on the two families of torus points in terms of the `sphericalTorusValue` recursion in $e_1,e_2,e_3$. The hypothesis `hbad` asserts, for every finite set $T$ of finite places: at each bad $v\in T$ the local Whittaker function is right invariant under some open subgroup of $GL_3(\mathbb{Q}_v)$, and every non-zero element of the cyclic subspace generated by `X.whittakerLoc v` generates a cyclic subspace containing `X.whittakerLoc v`. Further, `h1` normalises `X.whittakerLoc w 1 = 1` for $w\in S$; `hadm` asserts at each $w\in S$ that for every open subgroup $U_w$ the $U_w$-right-invariant vectors of the cyclic subspace lie in the span of a finite set of functions; `hcent` asserts at each $w\in S$ that the local component of `centralChar` is unitary and that `X.whittakerLoc w` transforms under the scalar matrices by that local component; `hψw` asserts that `psiLoc ψ w` has level $0$ for $w\in S$.
--
--   Integrability of the $S$-part. The hypotheses `hS` and `hS'` assert, for every admissible twist $\tau$ of $\mathbb{Q}$ and every $g$ in adelic $GL_3$, the existence of an abscissa beyond which, with respect to the $S$-part measure $\nu_S$ of [`NumberField.Idele.productMeasureData ℚ S`](def/NumberField_IdeleProductMeasure.html#L679), the integrands $a\mapsto X.\mathrm{whittaker}(\iota(\mathrm{diag}(a,1))g)\,\tau(a)\,\|a\|^{s-1}$, respectively the corresponding product of the archimedean integral of `dualWhittakerFn3` of `X.whittakerArch` along the lower unipotent with the normalised local integrals of `dualWhittakerFn3` of the `X.whittakerLoc v` over $v\in S$, times $\tau(a)\|a\|^{s-1}$, are integrable.
--
--   Archimedean splitting and parameters. Let $E$ be a homomorphism from the units of the infinite adeles to the ideles with `hE`: the infinite part of $E u$ is $u$ and its finite part is $1$. Let $\nu_{\mathrm{mul}}$ be a Haar measure on the units of the infinite adele ring. Let $u_R,a_R$ be families attached to the real places of $K$ (values in $\mathbb{C}$ and in $\mathbb{Z}/2$) and $u_C,k_C$ families attached to the complex places (values in $\mathbb{C}$ and $\mathbb{Z}$), such that by `hcR` and `hcC` the archimedean local components of $\mu$ at the real, respectively complex, places of $K$ are given by `IsArchCompAt` with these parameters. The hypothesis `hψQ` asserts $\psi^{-1}=$ [`NumberField.StandardAddChar.psiQ`](def/NumberField_StandardGlobalAddCharRat.html#L615).
--
--   The central twist $\omega_3$. Let $\omega_3$ be a homomorphism from the ideles of $\mathbb{Q}$ to $\mathbb{C}^\times$ with `hω₃`: it is an admissible twist; at every non-bad $p$ it is unramified and its Euler coefficient equals `inducedE3 ℚ (inducedCoeff K μ) p`; and for every choice of archimedean parameter families for $\mu$ as above, at every real place of $\mathbb{Q}$ the archimedean component of $\omega_3$ is given by `IsArchCompAt` with exponent $\sum_{w\ \mathrm{real}}u_R(w)+\sum_{w\ \mathrm{complex}}2u_C(w)$ and integer $\sum_{w\ \mathrm{real}}a_R(w)+\sum_{w\ \mathrm{complex}}(k_C(w)+1)$.
--
--   The archimedean additive data. Let $a\in\mathbb{Q}$ be non-zero, $a_\infty$ the corresponding unit of the infinite adeles (`haInf`), and `psiInf` the additive character $x\mapsto$ `psiArch`$(a\,x)$ (`hpsiInf`), which by `hψinf` is the restriction of $\psi$ to the infinite part. Let $\nu_{\mathrm{add}}$ be the measure $|a|^{1/2}$ times the transport of Lebesgue measure on the mixed space to the infinite adeles (`hν_add`).
--
--   The archimedean Whittaker package. Let `Warch` be a function on $GL_3$ of the infinite adeles; the hypothesis `hWarch` asserts, as a conjunction: `Warch` is non-zero, $K$-finite in the sense of `IsKFinite` (finitely many translates under the orthogonal set span), continuous and of rapid decay with exponent $t$ and arbitrary $N$ in terms of $\prod_w \mathrm{archRoot}_1\mathrm{archRoot}_2$ and $1+\mathrm{archRootSum}$; it satisfies the `psiInf`-Whittaker law; it transforms under the central scalars $z$ by $\omega_3(E z)$; for every admissible twist $\sigma$ of $\mathbb{Q}$ with archimedean parameters $(t,e)$ at the real place and every $g_\infty$, there exists an entire function $P$ such that (i) beyond some abscissa the archimedean zeta integral `archZeta30` $\nu_{\mathrm{mul}}$ of $h\mapsto$ `Warch`$(h g_\infty)$ against $\sigma\circ E$ converges and equals $P(s)$ times the `archFactor` of `heckeDatum K μ` with parameters $(u_R+t,\,a_R+e,\,u_C+t,\,k_C)$, that is, the product of the $\Gamma_{\mathbb{R}}$- and $\Gamma_{\mathbb{C}}$-factors built from those parameters; (ii) $P$ is of exponential growth in vertical strips; (iii) in every vertical strip and for every $N$, $|\operatorname{Im}s|^N$ times the norm of $P(s)$ times that archimedean factor is bounded for large $|\operatorname{Im}s|$; (iv) beyond some abscissa the dual integral `archZetaDual31` $\nu_{\mathrm{mul}},\nu_{\mathrm{add}}$ converges and, for $\operatorname{Re}(1-s)$ large, equals the product of $\prod_{w\ \mathrm{real\ of\ }K}\mathrm{signEpsilon}(a_R(w)+e)$, $\prod_{w\ \mathrm{complex}}i^{|k_C(w)|}$ and $\prod_{w}\mathrm{lambdaArch}\,K\,w$, times $\omega_3(E a_\infty)\,\sigma(E a_\infty)^3$, times $|a|^{3(s-1/2)}$, times $P(s)$, times the `archFactorDual` of the same `heckeDatum` at $1-s$; and finally, there exist an admissible twist $\sigma$ and a point $s$ at which `archZeta30` $\nu_{\mathrm{mul}}$ `Warch` $(\sigma\circ E)$ does not vanish. The hypothesis `hArchEq` identifies `X.whittakerArch` with `Warch`.
--
--   The deep set and the constants $\lambda_v$. Let $SQ\subseteq S$ (`hSQS`) be such that every prime of $K$ whose prime below is outside $SQ$ is unramified (`hSQ`), and such that every prime of $K$ above $SQ$ has conductor exponent at least $1$ for the local component of $\mu$ (`hdeep`). Let $\lambda$ be a complex-valued function on the finite places of $\mathbb{Q}$ with $\lambda_v=1$ for $v\notin S$ (`hlamoff`).
--
--   The hypothesis `hlamdeep` concerns $v\in SQ$ with `psiLoc ψ v` of level $0$: it asserts $\lambda_v\neq 0$, and moreover that for every local character $\eta$ of $\mathbb{Q}_v^\times$ with conductor exponent $c_\eta\le b$ such that every $w$ above $v$ satisfies $2\,e(w)b+1\le$ the conductor exponent of the local component of $\mu$ at $w$, every adelic admissible twist $\eta_A$ of $\mathbb{Q}$ whose local component at $v$ is $\eta$ and whose composition with the idelic norm of `genuineBaseChange ℚ K` is an admissible twist of $K$, and every integer $\ell$ equal to $\sum_{w\mid v} f(w)\cdot\mathrm{pinnedExp}\,K\,(\eta_A^{\mathrm{bc}}\mu)\,w$, the following holds: assuming the existence of a point $g_\infty$ and an admissible twist $\sigma$ with archimedean parameters $(t,e)$ satisfying $\eta(-1)=(-1)^e$ and with `archZeta30` of $h\mapsto X.\mathrm{whittakerArch}(h g_\infty)$ against $\sigma\circ E$ non-vanishing at points of arbitrarily large real part, then for all non-zero polynomials $R_1,R_2$ and all $m\in\mathbb{Z}$ such that at every $g\in GL_3(\mathbb{Q}_v)$ there are polynomials $Q_1,Q_2$ with $Q_2\neq 0$, an integer $n$ and abscissae for which the local zeta integrals `localZeta30` and `localZetaDual31` (taken against the multiplicative measure obtained from the self-dual additive measure at $v$) converge and satisfy $\zeta_0(s)Q_2(q^{-s})=Q_1(q^{-s})q^{ns}$ and $\zeta_{\mathrm{dual}}(1-s)Q_2(q^{-s})R_2(q^{-s})=R_1(q^{-s})Q_1(q^{-s})q^{(m+n)s}$, where $q=N(v)$, one has for every $s$
--   $$R_1(q^{-s})\,q^{ms}=\lambda_v\Bigl(\prod_{w\mid v}\chi_w(-1)\cdot\prod_{w\mid v}\mathrm{stdRootNumberAt}\,K\,w\,\chi_w\Bigr)q^{\ell(1/2-s)}R_2(q^{-s}),$$
--   with $\chi_w$ the local component at $w$ of $\eta_A^{\mathrm{bc}}\mu$.
--
--   The hypothesis `hlamtame` concerns $v\in S$ with $v\notin SQ$ and `psiLoc ψ v` of level $0$: for all non-zero polynomials $R_1,R_2$ and $m\in\mathbb{Z}$ satisfying the same two local zeta identities, now with the trivial local character in place of $\eta$, one has for every $s$
--   $$R_1(q^{-s})\,q^{ms}\,E^{\mu^{-1}}_v\bigl(q^{-(1-s)}\bigr)=\lambda_v\Bigl(\prod_{w\mid v}\mu_w(-1)\cdot\prod_{w\mid v}\mathrm{stdRootNumberAt}\,K\,w\,\mu_w\Bigr)q^{\,\mathrm{inducedLevelAt}\,K\,\mu\,v\,(1/2-s)}\,E^{\mu}_v(q^{-s})\,R_2(q^{-s}),$$
--   where $E^{\mu}_v$ and $E^{\mu^{-1}}_v$ denote the induced Euler polynomials `inducedEulerPoly ℚ` of `inducedCoeff K μ` and of `inducedCoeff K μ⁻¹` at $v$.
--
--   Conclusion. Under all of these hypotheses,
--   $$\Bigl(\prod_{v}^{\mathrm{fin}}\lambda_v^{2}\Bigr)\cdot\mathrm{lamSqArch}\,K=1,$$
--   the product being the multiplicative finite product over all finite places $v$ of $\mathbb{Q}$ of $\lambda_v^2$ (which is a genuine finite product because $\lambda_v=1$ off $S$), and $\mathrm{lamSqArch}\,K$ being $-1$ if the discriminant $\mathrm{discQ}\,K=\operatorname{discr}_{\mathbb{Q}}$ of a $\mathbb{Q}$-basis of $K$ is negative and $1$ otherwise.
--
--   This is the global product formula for the local discrepancy constants $\lambda_v$ attached to a cubic induction: comparing the $GL_3\times GL_1$ functional equation of the cubic induction data against the trivial twist with Tate's functional equation for $L(s,\mu)$, the finite places contribute $\prod_v\lambda_v^2$ and the archimedean places the sign $\lambda_\infty^2(K)$ determined by the sign of the discriminant of $K$. It is the bookkeeping half of the bad-place identification and is cited by [`LanglandsTunnell.CubicInduction.exists_forall_mem_gl3CyclicSubspace_localZetaDual31_eq_mul_of_isCubicInductionDataOn_deep_badPlaces`](thm.html#LanglandsTunnell.CubicInduction.exists_forall_mem_gl3CyclicSubspace_localZetaDual31_eq_mul_of_isCubicInductionDataOn_deep_badPlaces).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_finprod_sq_mul_lamSqArch_eq_one_of_forall_ne_zero_localZeta31_fe_rootNumber_of_isCubicInductionDataOn_of_archPackage_of_inv_eq_psiQ.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_LanglandsTunnell_LambdaSquared
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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal MeasureTheory LanglandsTunnell.RankinSelberg
open NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion LanglandsTunnell.CubicLambda

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in
open scoped Classical in

theorem LanglandsTunnell.CubicInduction.finprod_sq_mul_lamSqArch_eq_one_of_forall_ne_zero_localZeta31_fe_rootNumber_of_isCubicInductionDataOn_of_archPackage_of_inv_eq_psiQ
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
    (h1 : ∀ w ∈ S, X.whittakerLoc w 1 = 1)
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

    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSQS : SQ ⊆ S)
    (hSQ : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∉ SQ →
      Ideal.ramificationIdx' (𝔓.under (𝓞 ℚ)).asIdeal 𝔓.asIdeal = 1)
    (hdeep : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∈ SQ →
      1 ≤ LanglandsTunnell.TateLocal.conductorExponentAt K 𝔓 (localChar μ 𝔓))
    (lam : HeightOneSpectrum (𝓞 ℚ) → ℂ)
    (hlamoff : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → lam v = 1)

    (hlamdeep : ∀ v ∈ SQ, LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
        lam v ≠ 0 ∧
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
              lam v * ((∏ᶠ w ∈ primeFibre ℚ K v,
                  ((NumberField.TateGlobal.localChar
                    (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w (-1) : ℂˣ) : ℂ)) *
                ∏ᶠ w ∈ primeFibre ℚ K v,
                  LanglandsTunnell.TateLocal.stdRootNumberAt K w
                    (NumberField.TateGlobal.localChar
                      (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w)) *
              (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s)) * R₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) )

    (hlamtame : ∀ v ∈ S, v ∉ SQ → LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
      ∀ (R₁ R₂ : Polynomial ℂ) (m : ℤ), R₁ ≠ 0 → R₂ ≠ 0 →
      (∀ g : LocalGL3 v,
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
                (Ideal.absNorm v.asIdeal : ℂ) ^ (((m : ℂ) + (n : ℂ)) * s))) →
      ∀ s : ℂ,
        R₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s) *
            (inducedEulerPoly ℚ (inducedCoeff K μ⁻¹) v).eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))) =
          (lam v * ((∏ᶠ w ∈ primeFibre ℚ K v, ((NumberField.TateGlobal.localChar μ w (-1) : ℂˣ) : ℂ)) *
            ∏ᶠ w ∈ primeFibre ℚ K v, LanglandsTunnell.TateLocal.stdRootNumberAt K w (NumberField.TateGlobal.localChar μ w))) *
            (Ideal.absNorm v.asIdeal : ℂ) ^ ((inducedLevelAt K μ v : ℂ) * (1 / 2 - s)) *
            (inducedEulerPoly ℚ (inducedCoeff K μ) v).eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) *
            R₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))
    :
    (∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), lam v ^ 2) * lamSqArch K = 1 := by sorry
