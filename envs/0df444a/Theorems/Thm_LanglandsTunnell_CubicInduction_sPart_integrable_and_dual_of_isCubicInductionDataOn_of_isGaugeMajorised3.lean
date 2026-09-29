-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_sPart_integrable_and_dual_of_isCubicInductionDataOn_of_isGaugeMajorised3
-- name    : LanglandsTunnell.CubicInduction.sPart_integrable_and_dual_of_isCubicInductionDataOn_of_isGaugeMajorised3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/ade45a7b-58e4-55dd-b02a-e6e6f1dbaae7
-- title:
--   S-part integrability of the GL₃ zeta and dual integrands
-- statement:
--   Throughout, $K$ is a number field with $\operatorname{finrank}_{\mathbb Q}K=3$, equipped with an integral $\mathcal O_{\mathbb Q}$-algebra structure on $\mathcal O_K$; $\psi$ is an additive character of the adele ring of $\mathbb Q$ which is global in the sense of `IsGlobalAddChar` (trivial on principal adeles, continuous, non-trivial); and $\mu$ is a character of the idele group of $K$ which is an admissible twist, i.e. trivial on principal ideles, continuous and of absolute value $1$ everywhere.
--
--   Archimedean parameters for $\mu$: families $uR,aR$ indexed by the real places of $K$ (values in $\mathbb C$ and in $\mathbb Z/2$) and $uC,kC$ indexed by the complex places (values in $\mathbb C$ and in $\mathbb Z$), such that (`huR`) at each real place $w$ the archimedean local component of $\mu$ is $x\mapsto \|x\|^{\,\mathrm{mult}(w)\,uR_w}\,(x/\|x\|)^{(aR_w).\mathrm{val}}$ in the sense of `IsArchCompAt`, and (`huC`) at each complex place $w$ the same holds with exponents $uC_w$ and $kC_w$.
--
--   Level and non-induction hypotheses: `hlev` requires that at every finite place $v$ of $\mathbb Q$ the local character $\psi_v=$`psiLoc`$\,\psi\,v$ has `addCharLevel` equal to $0$, the level being the supremum of the integers $n$ for which $\psi_v$ is trivial on $\{x:\ v(x)\le \exp n\}$. The hypothesis `hns` is a negation: there is no admissible twist $\eta$ of the ideles of $\mathbb Q$ such that for every prime $\mathfrak P$ of $K$ at which $\mu$ is unramified and whose image $\mathfrak P\cap\mathcal O_{\mathbb Q}$ carries an unramified $\eta$, one has $\mu(\varpi_{\mathfrak P})=\eta(\varpi_{\mathfrak P\cap\mathcal O_{\mathbb Q}})^{f}$ with $f$ the inertia degree `inertiaDeg'` of $\mathfrak P$ over $\mathfrak P\cap\mathcal O_{\mathbb Q}$ and $\varpi$ the uniformizer idele.
--
--   Carrier data: a set $D$ of adelic $\mathrm{GL}_2$-points, a family $U$ of subgroups of adelic $\mathrm{GL}_2$ indexed by ideals of $\mathcal O_{\mathbb Q}$, and a family $gen$ of adelic $\mathrm{GL}_2$-points indexed by the finite places; these assemble, by `productionPinsOf`, into the carrier pins over $\mathbb Q$ whose measurable structures are the Borel ones, whose measures are the adelic $\mathrm{GL}_2$ Haar measure and the adelic additive Haar measure conditioned on the adelic box, and whose central subgroup is $\top$. A finite set $S$ of finite places of $\mathbb Q$ is prescribed by `hS` to consist exactly of the bad places for $(K,\mu)$, i.e. those ramified in $K$ or with $\mu$ twist-ramified above them.
--
--   The datum $X$ is a `CubicInductionData`: a function $X.\mathrm{form}$ on $\mathrm{GL}_3$ of the adeles of $\mathbb Q$, a global Whittaker function $X.\mathrm{whittaker}$, local functions $X.\mathrm{whittakerLoc}\,v$ on $\mathrm{GL}_3$ of each completion, an archimedean function $X.\mathrm{whittakerArch}$ on $\mathrm{GL}_3$ of the infinite adeles, a central character $X.\mathrm{centralChar}$ on the ideles, and a dual Whittaker function $X.\mathrm{dualWhittaker}$. The hypothesis `hX` asserts `IsCubicInductionDataOn` for $K$, the above pins, $\psi$, $\mu$ and $S$: its clauses (twenty-two, summarised here) require left invariance of $X.\mathrm{form}$ under the rational points, its central transformation law through $X.\mathrm{centralChar}$, which is an idele class character, cuspidality along the two maximal parabolics $P_{21}$ and $P_{12}$, the identification of $X.\mathrm{whittaker}$ with the $\psi$-Whittaker transform of $X.\mathrm{form}$ together with the $\psi$-Whittaker law and the mirabolic expansion summing to $X.\mathrm{form}$, the corresponding $\psi_v$-Whittaker laws for the local functions, the factorisation $X.\mathrm{whittaker}(g)=X.\mathrm{whittakerArch}(g_\infty)\prod_{v\in T}X.\mathrm{whittakerLoc}\,v\,(g_v)$ whenever $T\supseteq S$ is finite and $g_v$ lies in the local maximal compact off $T$, the induced-spherical behaviour off $S$ with respect to the induced coefficients of $\mu$, invariance under the congruence subgroup of the induced level at places off $S$ unramified in $K$, local Whittaker multiplicity one, moderate growth of $X.\mathrm{form}$, $K_\infty$-finiteness of $X.\mathrm{whittakerArch}$, iota moments and a Whittaker half-plane property, and the analogous clauses for $X.\mathrm{dualWhittaker}$ relative to $\psi^{-1}$ and the dual form.
--
--   Analytic and local hypotheses on $X$: continuity of $X.\mathrm{form}$, of $X.\mathrm{whittaker}$ and of $X.\mathrm{dualWhittaker}$ (`hcont`, `hcontW`, `hcontW'`); gauge majorisation `IsGaugeMajorised3` for $X.\mathrm{whittaker}$ and for $X.\mathrm{dualWhittaker}$, that is, existence of $t\in\mathbb N$, a finite set $T$ of finite places and $B\in\mathbb R$ such that for every $N$ there is $C$ with the function vanishing off the root-level set determined by $(T,B)$ and bounded there by $C/(\mathrm{rootSizeProd}(g)^t(1+\mathrm{archRootSum}(g))^N)$; and $X.\mathrm{whittakerArch}\neq 0$. The hypothesis `hatS` requires at each $w\in S$ four properties of $W_w:=X.\mathrm{whittakerLoc}\,w$: $W_w(1)=1$; every non-zero $F$ in the cyclic subspace spanned by the right translates of $W_w$ has $W_w$ in its own cyclic subspace; $W_w$ is right invariant under some open subgroup; and for every open subgroup $U_w$ there is a finite set $B$ of functions whose span contains every right $U_w$-invariant element of the cyclic subspace of $W_w$. The hypothesis `hcent` requires at each $w\in S$ that the local component of $X.\mathrm{centralChar}$ at $w$ be of absolute value $1$ and that $W_w(\mathrm{scalar}(t)h)=\omega_w(t)W_w(h)$. The hypothesis `hωcond` requires, at each finite place $v$ of $\mathbb Q$ not ramified in $K$, the existence of $a$ at most the induced level $\mathrm{inducedLevelAt}\,K\,\mu\,v$ with `HasConductorExponentAt` $\mathbb Q$ $v$ for the local component of $X.\mathrm{centralChar}$ and exponent $a$.
--
--   Archimedean normalisations: a monoid homomorphism $E$ from the infinite idele units to the idele units which (`hE`) splits the infinite part, $\mathrm{infPart}(E u)=u$ and $\mathrm{finPart}(E u)=1$; a non-zero rational $a$, an infinite idele unit $a_\infty$ whose underlying element is the image of $a$, and the additive character $\psi_\infty$ of the infinite adeles given by $\psi_\infty(x)=\mathrm{psiArch}(a\,x)$, with `hψinf` asserting that the restriction of $\psi$ along the inclusion of the infinite adeles into the adeles equals $\psi_\infty$. Borel measurable structures on the infinite adeles and their unit group are fixed; $\nu_{\mathrm{add}}$ is the measure $|a|^{1/2}$ times the pushforward of the volume of the mixed space along the inverse of `InfiniteAdeleRing.ringEquiv_mixedSpace`, and $\nu_{\mathrm{mul}}$ is a Haar measure on the infinite idele units.
--
--   The hypothesis `hArch` is a conjunction of five archimedean requirements on $W_\infty:=X.\mathrm{whittakerArch}$. First, $W_\infty$ is continuous and there is $t\in\mathbb N$ such that for every $N$ there is $C$ with $\|W_\infty(g_\infty)\|\le C/\big((\prod_{w}\mathrm{archRoot}_1(w,g)\,\mathrm{archRoot}_2(w,g))^t(1+\mathrm{archRootSum}(g))^N\big)$ for all adelic $g$. Second, $W_\infty$ satisfies the $\psi_\infty$-Whittaker law `IsGL3PsiWhittakerFn`. Third, $W_\infty(\mathrm{scalar}(z)g)=X.\mathrm{centralChar}(E z)\,W_\infty(g)$ for all infinite idele units $z$. Fourth, for every admissible twist $\sigma$ of the ideles of $\mathbb Q$, every $t\in\mathbb C$, $e\in\mathbb Z$ such that $\sigma$ has archimedean component $(t,e)$ at every real place of $\mathbb Q$, and every $g_\infty\in\mathrm{GL}_3$ of the infinite adeles, there is an entire function $P$ such that: the archimedean zeta integral $\mathrm{archZeta30}$ of $h\mapsto W_\infty(h g_\infty)$ against $\sigma\circ E$ converges for $\operatorname{Re}s>\sigma_0$ and equals $P(s)$ times the archimedean factor of the $L$-datum $\mathrm{heckeDatum}\,K\,\mu$ with parameters $(uR+t,\ aR+e,\ uC+t,\ kC)$; $P$ is of at most exponential growth in vertical strips; the product of $P$ with that archimedean factor decays faster than any power of $|\operatorname{Im}s|$ in vertical strips; and there is $\sigma_1$ with the dual convergence `IsArchZeta31ConvergentAbove` for the dual Whittaker function of $h\mapsto W_\infty(hg_\infty)$, $(\sigma\circ E)^{-1}$ and $\mathrm{weylPrime3}\cdot\mathrm{transposeInv3}\,1$, such that for $\operatorname{Re}(1-s)>\sigma_1$ the dual integral $\mathrm{archZetaDual31}(1-s)$ equals the product of the constant $\big(\prod_{w\ \mathrm{real}}\mathrm{signEpsilon}(aR_w+e)\big)\big(\prod_{w\ \mathrm{complex}}i^{|kC_w|}\big)\prod_{w}\lambda_{\mathrm{arch}}(K,w)$, of $X.\mathrm{centralChar}(E a_\infty)\,\sigma(E a_\infty)^3$, of $|a|^{3(s-1/2)}$, of $P(s)$, and of the dual archimedean factor of the same Hecke datum at $1-s$. Fifth, there exist an admissible twist $\sigma$ of $\mathbb Q$ and $s\in\mathbb C$ with $\mathrm{archZeta30}\,\nu_{\mathrm{mul}}\,W_\infty\,(\sigma\circ E)\,s\,1\neq0$.
--
--   Under these hypotheses two statements hold, both relative to the measure $\nu_S$ of the idelic product measure data [`NumberField.Idele.productMeasureData`](def/NumberField_IdeleProductMeasure.html#L679) $\mathbb Q$ $S$, the $S$-part measure on the idele units of $\mathbb Q$.
--
--   First: for every admissible twist $\tau$ of the ideles of $\mathbb Q$ and every $g\in\mathrm{GL}_3$ of the adeles of $\mathbb Q$ there is $\sigma_0\in\mathbb R$ such that for all $s$ with $\operatorname{Re}s>\sigma_0$ the function
--   $$a\ \longmapsto\ X.\mathrm{whittaker}\big(\iota(\mathrm{diag}(a,1))\,g\big)\,\tau(a)\,\|a\|^{s-1}$$
--   is $\nu_S$-integrable, where $\iota$ is the embedding of $\mathrm{GL}_2$ into $\mathrm{GL}_3$ as $h\mapsto\mathrm{diag}(h,1)$, $\mathrm{diag}(a,1)$ is `diagUnitGL2`, and $\|\cdot\|$ is the idele norm `TateGlobal.ideleNorm`.
--
--   Second: for every admissible twist $\tau$ of the ideles of $\mathbb Q$ and every $g$ as above there is $\sigma_0\in\mathbb R$ such that for all $s$ with $\operatorname{Re}s>\sigma_0$ the function
--   $$a\ \longmapsto\ A_\infty(a)\cdot\Big(\prod_{v\in S}c_v^{-1}A_v(a)\Big)\cdot\tau(a)\,\|a\|^{s-1}$$
--   is $\nu_S$-integrable, where $A_\infty(a)$ is the integral over the mixed space of $\mathbb Q$, with respect to its volume, of
--   $$y\ \longmapsto\ \widetilde W_\infty\big(\iota(\mathrm{diag}(a,1))_\infty\cdot n_{21}(\rho^{-1}(y))\cdot g_\infty\big),$$
--   with $\widetilde W_\infty=\mathrm{dualWhittakerFn3}\,X.\mathrm{whittakerArch}$, that is $h\mapsto X.\mathrm{whittakerArch}(\mathrm{longWeyl3}\cdot\mathrm{transposeInv3}\,h)$, with $n_{21}(x)$ the lower unipotent matrix `lowerUnipotent21` with entry $x$ in position $(2,1)$, with $\rho^{-1}$ the inverse of `InfiniteAdeleRing.ringEquiv_mixedSpace`, and with subscript $\infty$ denoting the archimedean component `archComponent3`; and where for $v\in S$, $A_v(a)$ is the integral over the completion at $v$, with respect to the self-dual Haar measure `selfDualHaarAt`, of
--   $$x\ \longmapsto\ \widetilde W_v\big(\iota(\mathrm{diag}(a,1))_v\cdot n_{21}(x)\cdot g_v\big),$$
--   with $\widetilde W_v=\mathrm{dualWhittakerFn3}\,(X.\mathrm{whittakerLoc}\,v)$ and subscript $v$ denoting the component `componentAt3` at $v$, and $c_v$ is the measure of the local integers under that self-dual Haar measure, viewed in $\mathbb C$.
--
--   The abscissa $\sigma_0$ is allowed to depend on $\tau$ and $g$ in both conjuncts.
--
--   This is the half-plane convergence input for the global zeta integrals attached to cubic induction data on $\mathrm{GL}_3$ over $\mathbb Q$ and to their partial Fourier transforms in the $(2,1)$ unipotent coordinate, in the shape in which the later extraction and identification steps for the local zeta factors require it. It packages the two separate integrability statements [`LanglandsTunnell.CubicInduction.sPart_integrable_of_isCubicInductionDataOn_of_isGaugeMajorised3`](thm.html#LanglandsTunnell.CubicInduction.sPart_integrable_of_isCubicInductionDataOn_of_isGaugeMajorised3) and [`LanglandsTunnell.CubicInduction.sPartDual_integrable_of_isCubicInductionDataOn_of_isGaugeMajorised3`](thm.html#LanglandsTunnell.CubicInduction.sPartDual_integrable_of_isCubicInductionDataOn_of_isGaugeMajorised3), and is cited by the theorems that compute the local zeta and dual zeta integrals at the bad places and at places ramified in $K$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_sPart_integrable_and_dual_of_isCubicInductionDataOn_of_isGaugeMajorised3.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_RSCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal MeasureTheory LanglandsTunnell.RankinSelberg
  LanglandsTunnell.CubicLambda

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in
open scoped Classical in

theorem LanglandsTunnell.CubicInduction.sPart_integrable_and_dual_of_isCubicInductionDataOn_of_isGaugeMajorised3
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (huR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (huC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
    (hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (hns : ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hS : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w ↔ w ∈ S)
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ
      (S : Set (HeightOneSpectrum (𝓞 ℚ))) X)
    (hcont : Continuous X.form) (hcontW : Continuous X.whittaker) (hcontW' : Continuous X.dualWhittaker)
    (hW : IsGaugeMajorised3 ℚ X.whittaker) (hW' : IsGaugeMajorised3 ℚ X.dualWhittaker)
    (hne : X.whittakerArch ≠ 0)
    (hatS : ∀ w ∈ S, X.whittakerLoc w 1 = 1 ∧
      (∀ F ∈ gl3CyclicSubspace (X.whittakerLoc w), F ≠ 0 → X.whittakerLoc w ∈ gl3CyclicSubspace F) ∧
      (∃ Uw : Subgroup (LocalGL3 w), IsOpen (Uw : Set (LocalGL3 w)) ∧
        ∀ k ∈ Uw, ∀ g : LocalGL3 w, X.whittakerLoc w (g * k) = X.whittakerLoc w g) ∧
      ∀ Uw : Subgroup (LocalGL3 w), IsOpen (Uw : Set (LocalGL3 w)) →
        ∃ B : Finset (LocalGL3 w → ℂ), ∀ F ∈ gl3CyclicSubspace (X.whittakerLoc w),
          (∀ k ∈ Uw, ∀ g : LocalGL3 w, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 w → ℂ)))
    (hcent : ∀ w ∈ S,
      (∀ z : (w.adicCompletion ℚ)ˣ, ‖((localChar X.centralChar w z : ℂˣ) : ℂ)‖ = 1) ∧
      ∀ (t : (w.adicCompletion ℚ)ˣ) (h : LocalGL3 w),
        X.whittakerLoc w (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) =
          ((localChar X.centralChar w t : ℂˣ) : ℂ) * X.whittakerLoc w h)
    (hωcond : ∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsRamifiedIn K v → ∃ a ≤ inducedLevelAt K μ v,
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (localChar X.centralChar v) a)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ, M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (a : ℚ) (ha : a ≠ 0) (aInf : (InfiniteAdeleRing ℚ)ˣ)
    (haInf : (aInf : InfiniteAdeleRing ℚ) = algebraMap ℚ (InfiniteAdeleRing ℚ) a)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (hψinf : ψ.compAddMonoidHom
        (AddMonoidHom.inl (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)) = psiInf)
    [mA : MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_add : MeasureTheory.Measure (InfiniteAdeleRing ℚ))
    (hν_add : ν_add = ENNReal.ofReal (|(a : ℝ)| ^ ((1 : ℝ) / 2)) •
      MeasureTheory.Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm MeasureTheory.volume)
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (hArch :
      (Continuous X.whittakerArch ∧ ∃ t : ℕ, ∀ N : ℕ, ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ‖X.whittakerArch (archComponent3 (𝓞 ℚ) ℚ g)‖ ≤
        C / ((∏ w : InfinitePlace ℚ, archRoot₁ ℚ w g * archRoot₂ ℚ w g) ^ t * (1 + archRootSum ℚ g) ^ N)) ∧
      IsGL3PsiWhittakerFn psiInf X.whittakerArch ∧
      (∀ (z : (InfiniteAdeleRing ℚ)ˣ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)),
        X.whittakerArch (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((X.centralChar (E z) : ℂˣ) : ℂ) * X.whittakerArch g) ∧
      (∀ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ →
        ∀ (t : ℂ) (e : ℤ), (∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v t e) →
        ∀ gInf : GL (Fin 3) (InfiniteAdeleRing ℚ), ∃ P : ℂ → ℂ, Differentiable ℂ P ∧
          (∃ σ₀ : ℝ, IsArchZeta30ConvergentAbove ν_mul (fun h => X.whittakerArch (h * gInf)) (σ.comp E) 1 σ₀ ∧
            ∀ s : ℂ, σ₀ < s.re →
              archZeta30 ν_mul (fun h => X.whittakerArch (h * gInf)) (σ.comp E) s 1 =
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
          (∃ σ₁ : ℝ, IsArchZeta31ConvergentAbove ν_mul ν_add (dualWhittakerFn3 (fun h => X.whittakerArch (h * gInf)))
              (σ.comp E)⁻¹ (weylPrime3 * transposeInv3 1) σ₁ ∧
            ∀ s : ℂ, σ₁ < (1 - s).re →
              archZetaDual31 ν_mul ν_add (fun h => X.whittakerArch (h * gInf)) (σ.comp E) (1 - s) 1 =
                (((Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).prod
                    fun w => signEpsilon (aR w.1 w.2 + (e : ZMod 2))) *
                  ((Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).prod
                      fun w => Complex.I ^ (kC w.1 w.2).natAbs) *
                  ∏ w : InfinitePlace K, lambdaArch K w) *
                (((X.centralChar (E aInf) : ℂˣ) : ℂ) * ((σ (E aInf) : ℂˣ) : ℂ) ^ 3) *
                (((|a| : ℝ) : ℂ) ^ (3 * (s - 1 / 2))) *
                P s *
                  (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
                    (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactorDual (1 - s))) ∧
      ∃ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ ∧
        ∃ s : ℂ, archZeta30 ν_mul X.whittakerArch (σ.comp E) s 1 ≠ 0)
 :
    (∀ τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ τ → ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ∃ σ₀ : ℝ,
      ∀ s : ℂ, σ₀ < s.re →
        Integrable (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
          X.whittaker (iotaGL (diagUnitGL2 a) * g) * ((τ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1))
          (NumberField.Idele.productMeasureData ℚ S).νS) ∧
    (∀ τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ τ → ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ∃ σ₀ : ℝ,
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
          (NumberField.Idele.productMeasureData ℚ S).νS) := by sorry
