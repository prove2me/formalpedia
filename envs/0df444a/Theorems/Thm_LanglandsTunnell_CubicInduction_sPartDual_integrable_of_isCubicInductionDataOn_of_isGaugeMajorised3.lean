-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_sPartDual_integrable_of_isCubicInductionDataOn_of_isGaugeMajorised3
-- name    : LanglandsTunnell.CubicInduction.sPartDual_integrable_of_isCubicInductionDataOn_of_isGaugeMajorised3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/93e61ce6-9fcf-5fd8-a06d-866540bc61c4
-- title:
--   Integrability of the dual S-part zeta integrand on GL₃
-- statement:
--   Throughout, $K$ is a number field which is an $\mathcal{O}_{\mathbb{Q}}$-algebra in an integral way, with $\operatorname{finrank}_{\mathbb{Q}} K = 3$ (`hdeg`).
--
--   **Additive character.** $\psi$ is an additive character of the adele ring $\mathbb{A}_{\mathbb{Q}}$ with values in $\mathbb{C}$, and `hψ` asserts `IsGlobalAddChar`: $\psi$ is trivial on the image of $\mathbb{Q}$, continuous, and non-trivial. The hypothesis `hlev` asserts that at every finite place $v$ the local character $\mathrm{psiLoc}\,\psi\,v$ (the restriction of $\psi$ along the single-place embedding $\mathbb{Q}_v \to \mathbb{A}_{\mathbb{Q}}$) has `addCharLevel` equal to $0$.
--
--   **The character of $K$ and its archimedean parameters.** $\mu : (\mathbb{A}_K)^\times \to \mathbb{C}^\times$ satisfies `hμ : IsAdmissibleTwist K μ`, i.e. $\mu$ is trivial on the principal ideles $K^\times$, continuous, and of absolute value $1$ everywhere. Data $uR, aR$ (indexed by the real places, with values in $\mathbb{C}$ and in $\mathbb{Z}/2$) and $uC, kC$ (indexed by the complex places, with values in $\mathbb{C}$ and in $\mathbb{Z}$) are subject to `huR` and `huC`: for each real $w$ the archimedean local component of $\mu$ at $w$ is $x \mapsto \|x\|^{\,\mathrm{mult}(w)\cdot uR_w}\,(\iota_w(x)/\|x\|)^{(aR_w).\mathrm{val}}$, and for each complex $w$ it is $x \mapsto \|x\|^{\,\mathrm{mult}(w)\cdot uC_w}\,(\iota_w(x)/\|x\|)^{kC_w}$, in the sense of `IsArchCompAt`. The hypothesis `hns` asserts that $\mu$ is not of base-change shape: there is no admissible twist $\eta$ of $\mathbb{Q}$ such that, for every prime $\mathfrak{P}$ of $K$ at which $\mu$ is unramified and lying over a prime of $\mathbb{Q}$ at which $\eta$ is unramified, $\mu$ of a uniformiser idele at $\mathfrak{P}$ equals $\eta$ of a uniformiser idele at $\mathfrak{P}\cap\mathcal{O}_{\mathbb{Q}}$ raised to the inertia degree $f(\mathfrak{P}/p)$.
--
--   **Carrier data and the bad set.** $D$ is a subset of $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, $U$ assigns to each ideal of $\mathcal{O}_{\mathbb{Q}}$ a subgroup of $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, and $\mathrm{gen}$ assigns an element of $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ to each finite place; these enter only through the carrier pins $\mathrm{productionPinsOf}\ \mathbb{Q}\ D\ U\ \mathrm{gen}\ (\mathrm{adelicBox}\ \mathbb{Q})$, whose measure-theoretic fields are the Borel structures and Haar measures on $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ and on $\mathbb{A}_{\mathbb{Q}}$ conditioned on the adelic box, with full central subgroup. The finite set $S$ of finite places satisfies `hS`: $w \in S$ if and only if $w$ is a bad place for $(K,\mu)$, i.e. $w$ is ramified in $K$ or $\mu$ is twist-ramified above $w$.
--
--   **The cubic induction data.** $X : \mathrm{CubicInductionData}$ consists of a form $X.\mathrm{form}$ on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$, a global Whittaker function $X.\mathrm{whittaker}$, local Whittaker functions $X.\mathrm{whittakerLoc}\,v$ on $\mathrm{GL}_3(\mathbb{Q}_v)$, an archimedean Whittaker function $X.\mathrm{whittakerArch}$ on $\mathrm{GL}_3$ of the infinite adeles, a central character $X.\mathrm{centralChar}$ on $(\mathbb{A}_{\mathbb{Q}})^\times$, and a dual Whittaker function $X.\mathrm{dualWhittaker}$. The hypothesis `hX : IsCubicInductionDataOn` (twenty-two clauses, summarised here) requires: left invariance of $X.\mathrm{form}$ under the rational points, its transformation by $X.\mathrm{centralChar}$ under the adelic centre, triviality of $X.\mathrm{centralChar}$ on $\mathbb{Q}^\times$, cuspidality along the two maximal parabolics $P_{21}$, $P_{12}$ for the given pins; that $X.\mathrm{whittaker}$ is the $\psi$-Whittaker integral of $X.\mathrm{form}$ and obeys the $\psi$-Whittaker transformation law under the upper unipotent, with mirabolic expansion summing to $X.\mathrm{form}$; the local Whittaker laws for $\mathrm{psiLoc}\,\psi\,v$, the factorisation $X.\mathrm{whittaker}(g) = X.\mathrm{whittakerArch}(g_\infty)\prod_{v \in T} X.\mathrm{whittakerLoc}\,v\,(g_v)$ for every finite $T \supseteq S$ with $g_v$ integral outside $T$, sphericity off $S$ of the type induced from the coefficients of $\mu$, invariance off $S$ at places unramified in $K$ under the congruence subgroup of level $\mathrm{inducedLevelAt}\,K\,\mu\,v$, local Whittaker multiplicity one, moderate growth of $X.\mathrm{form}$, $K$-finiteness of $X.\mathrm{whittakerArch}$, iota moments and a Whittaker half-plane; together with the dual counterparts: $X.\mathrm{dualWhittaker}$ is the $\psi^{-1}$-Whittaker integral of the dual form, obeys the $\psi^{-1}$-Whittaker law, has mirabolic expansion summing to the dual form, and satisfies iota moments and a half-plane condition.
--
--   **Analytic hypotheses on $X$.** `hcont`, `hcontW`, `hcontW'` assert continuity of $X.\mathrm{form}$, $X.\mathrm{whittaker}$ and $X.\mathrm{dualWhittaker}$. `hW` and `hW'` assert `IsGaugeMajorised3` for $X.\mathrm{whittaker}$ and for $X.\mathrm{dualWhittaker}$: there are $t \in \mathbb{N}$, a finite set $T$ of finite places and $B \in \mathbb{R}$ such that for each $N$ there is $C$ with the function vanishing outside the root level region determined by $(T,B)$ and bounded there by $C/(\mathrm{rootSizeProd}(g)^t (1+\mathrm{archRootSum}(g))^N)$. `hne` asserts $X.\mathrm{whittakerArch} \neq 0$.
--
--   **Local hypotheses at $S$.** `hatS` asserts, for each $w \in S$: $X.\mathrm{whittakerLoc}\,w\,(1) = 1$; every non-zero element $F$ of the cyclic subspace $\mathrm{gl3CyclicSubspace}(X.\mathrm{whittakerLoc}\,w)$ generates $X.\mathrm{whittakerLoc}\,w$ back, i.e. $X.\mathrm{whittakerLoc}\,w \in \mathrm{gl3CyclicSubspace}(F)$; $X.\mathrm{whittakerLoc}\,w$ is right invariant under some open subgroup of $\mathrm{GL}_3(\mathbb{Q}_w)$; and for every open subgroup $U_w$ there is a finite set $B$ of functions spanning the $U_w$-right-invariant elements of the cyclic subspace. `hcent` asserts, for each $w \in S$: the local component of $X.\mathrm{centralChar}$ at $w$ has absolute value $1$, and $X.\mathrm{whittakerLoc}\,w$ transforms by it under scalar matrices. `hωcond` asserts that at each finite place $v$ unramified in $K$ the local component of $X.\mathrm{centralChar}$ has a conductor exponent $a \le \mathrm{inducedLevelAt}\,K\,\mu\,v$ in the sense of `HasConductorExponentAt`.
--
--   **Archimedean splitting, scaling and measures.** $E$ is a monoid homomorphism from the units of the infinite adele ring to the idele group with `hE`: for every $u$, the infinite part of $E(u)$ is $u$ and the finite part of $E(u)$ is $1$. A non-zero $a \in \mathbb{Q}$ is given together with a unit $a_\infty$ of the infinite adele ring whose underlying element is the image of $a$ (`haInf`), and an additive character $\mathrm{psiInf}$ of the infinite adele ring with $\mathrm{psiInf}(x) = \mathrm{psiArch}(a x)$ (`hpsiInf`); `hψinf` asserts that the restriction of $\psi$ along the inclusion of the infinite adeles equals $\mathrm{psiInf}$. Borel measurable structures on the infinite adele ring and on its unit group are assumed. The measure $\nu_{\mathrm{add}}$ on the infinite adele ring is required by `hν_add` to be $|a|^{1/2}$ times the pushforward of the canonical volume under the inverse of the ring isomorphism with the mixed space of $\mathbb{Q}$, and $\nu_{\mathrm{mul}}$ is a Haar measure on the units of the infinite adele ring.
--
--   **The archimedean package `hArch`** (five groups of clauses, summarised here) requires: continuity of $X.\mathrm{whittakerArch}$ together with a moderate-growth bound, namely some $t \in \mathbb{N}$ such that for each $N$ there is $C$ with $\|X.\mathrm{whittakerArch}(g_\infty)\| \le C/\big((\prod_w \mathrm{archRoot}_1(w,g)\,\mathrm{archRoot}_2(w,g))^t (1+\mathrm{archRootSum}(g))^N\big)$; the $\mathrm{psiInf}$-Whittaker transformation law for $X.\mathrm{whittakerArch}$; transformation under scalar matrices by $X.\mathrm{centralChar} \circ E$; and, for every admissible twist $\sigma$ of $\mathbb{Q}$, every $t \in \mathbb{C}$, $e \in \mathbb{Z}$ with $\sigma$ having archimedean component of type $(t,e)$ at every real place, and every $g_\infty \in \mathrm{GL}_3$ of the infinite adeles, the existence of an entire function $P$ such that (i) the zeta integral $\mathrm{archZeta30}$ of $h \mapsto X.\mathrm{whittakerArch}(h g_\infty)$ against $\sigma \circ E$ converges in a half-plane $\mathrm{Re}\,s > \sigma_0$ and equals there $P(s)$ times the archimedean factor of the $L$-datum $\mathrm{heckeDatum}\,K\,\mu$ with parameters shifted to $(uR + t,\ aR + e,\ uC + t,\ kC)$; (ii) $P$ is of exponential type in vertical strips, $\|P(s)\| \le C \exp(A|\mathrm{Im}\,s|)$; (iii) the product of $P$ with that archimedean factor decays faster than any power of $|\mathrm{Im}\,s|$ in vertical strips; and (iv) the dual zeta integral converges for $\mathrm{Re}(1-s) > \sigma_1$ and satisfies the functional equation in which $\mathrm{archZetaDual31}$ at $1-s$ equals the product of the sign constants $\prod_{w \text{ real}} \mathrm{signEpsilon}(aR_w + e)$, $\prod_{w \text{ complex}} i^{|kC_w|}$ and $\prod_{w} \mathrm{lambdaArch}\,K\,w$, times $X.\mathrm{centralChar}(E a_\infty)\,\sigma(E a_\infty)^3$, times $|a|^{3(s-1/2)}$, times $P(s)$, times the dual archimedean factor of the same $L$-datum at $1-s$. Finally `hArch` requires that for some admissible twist $\sigma$ of $\mathbb{Q}$ and some $s$ the integral $\mathrm{archZeta30}\ \nu_{\mathrm{mul}}\ X.\mathrm{whittakerArch}\ (\sigma \circ E)\ s\ 1$ is non-zero.
--
--   **Conclusion.** For every monoid homomorphism $\tau : (\mathbb{A}_{\mathbb{Q}})^\times \to \mathbb{C}^\times$ which is an admissible twist of $\mathbb{Q}$ (trivial on $\mathbb{Q}^\times$, continuous, unitary) and for every $g \in \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ there exists $\sigma_0 \in \mathbb{R}$ such that for every $s \in \mathbb{C}$ with $\sigma_0 < \mathrm{Re}\,s$ the function of the idele $a$ given by
--   $$\Big(\int_{y} \widetilde{X.\mathrm{whittakerArch}}\big((\iota(\mathrm{diag}(a,1)))_\infty \cdot u_{21}(y') \cdot g_\infty\big)\Big) \cdot \prod_{v \in S} c_v^{-1} \int_{\mathbb{Q}_v} \widetilde{X.\mathrm{whittakerLoc}\,v}\big((\iota(\mathrm{diag}(a,1)))_v \cdot u_{21}(x) \cdot g_v\big)\, d(\mathrm{selfDualHaarAt}\ \mathbb{Q}\ v) \cdot \tau(a) \cdot \mathrm{ideleNorm}(a)^{s-1}$$
--   is integrable with respect to the measure $\nu_S$ of $\mathrm{productMeasureData}\ \mathbb{Q}\ S$, that is, with respect to the $S$-part measure $\mathrm{sPartMeasure}\ \mathbb{Q}\ S$ on the idele group. Here: $\mathrm{diag}(a,1)$ is $\mathrm{diagUnitGL2}\,a$ and $\iota$ is the block embedding $\mathrm{iotaGL} : \mathrm{GL}_2 \to \mathrm{GL}_3$; $u_{21}(x) = \mathrm{lowerUnipotent21}(x)$ is the unipotent matrix with entry $x$ in position $(2,1)$; the tilde denotes $\mathrm{dualWhittakerFn3}$, so $\widetilde{W}(h) = W(w_3 \cdot {}^{t}h^{-1})$ with $w_3 = \mathrm{longWeyl3}$ and ${}^{t}h^{-1} = \mathrm{transposeInv3}(h)$; the archimedean integral is over the mixed space of $\mathbb{Q}$ with respect to its canonical volume, $y'$ being the image of $y$ under the inverse of the ring isomorphism between the infinite adeles and the mixed space; the subscripts $\infty$ and $v$ denote the maps $\mathrm{archComponent3}$ and $\mathrm{componentAt3}\ v$; $c_v$ is the real number $(\mathrm{selfDualHaarAt}\ \mathbb{Q}\ v)(\mathcal{O}_v)$, coerced to $\mathbb{C}$; and $\mathrm{ideleNorm}\ \mathbb{Q}\ a$ is the module of $a$, i.e. the value at $a$ of the distributive Haar character of $\mathbb{A}_{\mathbb{Q}}$. The conclusion asserts integrability only, with no formula for the integral.
--
--   This is the convergence statement for the $S$-part of the dual global zeta integral attached to cubic induction data on $\mathrm{GL}_3$ over $\mathbb{Q}$: the integrand is the $(a,x)$-integrated dual Whittaker function, factorised into an archimedean integral over the mixed space and local integrals at the bad places, twisted by an admissible character $\tau$ and by $|a|^{s-1}$. It feeds the companion result [`LanglandsTunnell.CubicInduction.sPart_integrable_and_dual_of_isCubicInductionDataOn_of_isGaugeMajorised3`](thm.html#LanglandsTunnell.CubicInduction.sPart_integrable_and_dual_of_isCubicInductionDataOn_of_isGaugeMajorised3), which assembles the zeta integral and its dual in the converse-theorem argument behind the Langlands–Tunnell step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_sPartDual_integrable_of_isCubicInductionDataOn_of_isGaugeMajorised3.lean

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

theorem LanglandsTunnell.CubicInduction.sPartDual_integrable_of_isCubicInductionDataOn_of_isGaugeMajorised3
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
    ∀ τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ τ → ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ∃ σ₀ : ℝ,
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
          (NumberField.Idele.productMeasureData ℚ S).νS := by sorry
