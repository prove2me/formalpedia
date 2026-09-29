-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isArchZeta31ConvergentAbove_dualWhittakerFn3_whittakerArch_of_isCubicInductionDataOn
-- name    : LanglandsTunnell.CubicInduction.exists_isArchZeta31ConvergentAbove_dualWhittakerFn3_whittakerArch_of_isCubicInductionDataOn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/9ebffffc-819c-5c65-9880-b495f76d545c
-- title:
--   Convergence of the dual archimedean GL₃ zeta integral at the trivial twist
-- statement:
--   Setting. Let $K$ be a number field with an $\mathcal O_{\mathbb Q}$-algebra structure on $\mathcal O_K$ making $\mathcal O_K$ integral over $\mathcal O_{\mathbb Q}$, and assume $[K:\mathbb Q]=3$ (`hdeg`). Let $\psi$ be an additive character of the adele ring of $\mathbb Q$ which is a global additive character in the sense of `IsGlobalAddChar`: trivial on the principal adeles $\psi(\alpha)=1$ for $\alpha\in\mathbb Q$, continuous, and non-trivial. Let $\mu$ be a character of the idele group of $K$ which is an admissible twist (`IsAdmissibleTwist`): trivial on the principal ideles $K^\times$, continuous, and unitary.
--
--   Archimedean parameters of $\mu$. Families $uR, aR$ indexed by the real places and $uC, kC$ indexed by the complex places of $K$, with values in $\mathbb C$, $\mathbb Z/2$, $\mathbb C$, $\mathbb Z$ respectively, are given such that (`huR`, `huC`) at each real place $w$ the archimedean local component of $\mu$ is $x\mapsto \|x\|^{\mathrm{mult}(w)\,uR_w}\,(x/\|x\|)^{\,\overline{aR_w}}$, where $\overline{aR_w}\in\{0,1\}$ is the integer lift of $aR_w$, and at each complex place $w$ it is $x\mapsto \|x\|^{\mathrm{mult}(w)\,uC_w}\,(x/\|x\|)^{kC_w}$ (`IsArchCompAt`).
--
--   Level and non-degeneracy. The hypothesis `hlev` requires that at every finite place $v$ of $\mathbb Q$ the local component `psiLoc ψ v` has `addCharLevel` equal to $0$. The hypothesis `hns` requires that no admissible twist $\eta$ of the ideles of $\mathbb Q$ satisfies: for every prime $\mathfrak P$ of $K$ at which $\mu$ is unramified and such that $\eta$ is unramified at the prime of $\mathbb Q$ below $\mathfrak P$, the value $\mu$ at the uniformizer idele of $\mathfrak P$ equals the value of $\eta$ at the uniformizer idele of $\mathfrak P\cap\mathcal O_{\mathbb Q}$ raised to the inertia degree of $\mathfrak P$ over that prime.
--
--   Carrier data and bad places. A set $D$ of adelic $\mathrm{GL}_2$-matrices over $\mathbb Q$, a family $U$ of subgroups indexed by ideals of $\mathcal O_{\mathbb Q}$, a family `gen` of adelic $\mathrm{GL}_2$-matrices indexed by the finite places, and a finite set $S$ of finite places of $\mathbb Q$ are given, with `hS` asserting that $S$ consists exactly of the bad places of $(K,\mu)$, that is the places ramified in $K$ together with the places under which $\mu$ is twist-ramified.
--
--   Cubic induction data. Let $X$ be a `CubicInductionData`, i.e. a tuple $X=(\mathrm{form},\ \mathrm{whittaker},\ (\mathrm{whittakerLoc}_v)_v,\ \mathrm{whittakerArch},\ \mathrm{centralChar},\ \mathrm{dualWhittaker})$ consisting of two complex-valued functions on $\mathrm{GL}_3$ of the adeles of $\mathbb Q$, a family of complex-valued functions on the local groups $\mathrm{GL}_3$ of the completions, a complex-valued function on $\mathrm{GL}_3$ of the infinite adeles, a character of the idele group of $\mathbb Q$, and a further function on the adelic $\mathrm{GL}_3$. The hypothesis `hX` asserts `IsCubicInductionDataOn` for $K$, the carrier pins `productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)` (the Borel structure and Haar measure on the adelic $\mathrm{GL}_2$, the set $D$, full central subgroup, the families $U$ and `gen`, the adelic Borel structure, and the Haar measure conditioned on the adelic box), the character $\psi$, the character $\mu$ and the set $S$. Its twenty-two clauses are summarised here: $X.\mathrm{form}$ is invariant under left translation by $\mathrm{GL}_3(\mathbb Q)$, transforms under central scalars by $X.\mathrm{centralChar}$, which is trivial on principal ideles, and is cuspidal along the two parabolics $P_{21}$ and $P_{12}$ relative to the pins; $X.\mathrm{whittaker}$ is the $\psi$-Whittaker integral of $X.\mathrm{form}$, satisfies the $\psi$-Whittaker law $W(u(x,y,z)g)=\psi(x+y)W(g)$ for upper unipotent $u(x,y,z)$, and its translates over the mirabolic index set sum to $X.\mathrm{form}$; each $X.\mathrm{whittakerLoc}_v$ satisfies the Whittaker law for `psiLoc ψ v` and has local multiplicity one; $X.\mathrm{whittaker}$ factorises as $X.\mathrm{whittakerArch}$ at the archimedean component times the product of the $X.\mathrm{whittakerLoc}_v$ over any finite set $T\supseteq S$ containing all places where the component leaves the maximal compact; off $S$ the local functions are spherical of the induced type attached to `inducedCoeff K μ`, and at places off $S$ unramified in $K$ they are right invariant under the congruence subgroup `congruenceK1` of level `inducedLevelAt K μ v`; $X.\mathrm{form}$ has moderate growth, $X.\mathrm{whittakerArch}$ is $K$-finite, and $X.\mathrm{form}$, $X.\mathrm{whittaker}$ satisfy the iota-moment and Whittaker half-plane conditions; finally $X.\mathrm{dualWhittaker}$ is the $\psi^{-1}$-Whittaker integral of the dual form, satisfies the $\psi^{-1}$-Whittaker law, its mirabolic translates sum to the dual form, and the dual form and $X.\mathrm{dualWhittaker}$ satisfy the corresponding iota-moment and half-plane conditions.
--
--   Regularity and growth. The hypotheses `hcont`, `hcontW`, `hcontW'` require $X.\mathrm{form}$, $X.\mathrm{whittaker}$ and $X.\mathrm{dualWhittaker}$ to be continuous; `hW` and `hW'` require $X.\mathrm{whittaker}$ and $X.\mathrm{dualWhittaker}$ to be gauge-majorised in the sense of `IsGaugeMajorised3` (vanishing outside a root level, with bounds $C/(\text{root size product}^{\,t}(1+\text{arch root sum})^N)$ inside it); `hne` requires $X.\mathrm{whittakerArch}\neq 0$.
--
--   Local conditions at bad places. The hypothesis `hatS` requires, for each $w\in S$: $X.\mathrm{whittakerLoc}_w(1)=1$; every non-zero $F$ in the cyclic subspace `gl3CyclicSubspace` generated by $X.\mathrm{whittakerLoc}_w$ under right translation has $X.\mathrm{whittakerLoc}_w$ in its own cyclic subspace; $X.\mathrm{whittakerLoc}_w$ is right invariant under some open subgroup of the local $\mathrm{GL}_3$; and for every open subgroup $U_w$ there is a finite set $B$ of functions whose complex span contains all $U_w$-right-invariant elements of that cyclic subspace. The hypothesis `hcent` requires, for each $w\in S$, that the local component `localChar X.centralChar w` be of absolute value $1$ on local units and that $X.\mathrm{whittakerLoc}_w$ transform under scalar matrices by this local character. The hypothesis `hωcond` requires, for every finite place $v$ of $\mathbb Q$ not ramified in $K$, the existence of $a\le$ `inducedLevelAt K μ v` with `HasConductorExponentAt ℚ v (localChar X.centralChar v) a`.
--
--   Archimedean splitting, the additive character at infinity, and measures. A monoid homomorphism $E$ from the units of the infinite adeles of $\mathbb Q$ to the idele group is given with `hE`: the infinite part of $E(u)$ is $u$ and its finite part is $1$. A non-zero rational $a$ is given (`ha`), together with an infinite idele $a_\infty$ whose underlying infinite adele is the image of $a$ (`haInf`), and an additive character `psiInf` of the infinite adeles with `psiInf`$(x)=\mathrm{psiArch}(a\cdot x)$ (`hpsiInf`); `hψinf` requires that the restriction of $\psi$ along the inclusion of the infinite adeles into the adeles be `psiInf`. Measures $\nu_{\mathrm{add}}$ on the infinite adeles and $\nu_{\mathrm{mul}}$ on its unit group are given, with measurable and Borel structures, $\nu_{\mathrm{add}}=|a|^{1/2}$ times the pushforward of Lebesgue measure under the inverse of the ring equivalence with the mixed space (`hν_add`), and $\nu_{\mathrm{mul}}$ a Haar measure.
--
--   The archimedean package `hArch`. This is a conjunction of five clauses. (i) $X.\mathrm{whittakerArch}$ is continuous and there is $t\in\mathbb N$ such that for every $N$ there is $C$ with $\|X.\mathrm{whittakerArch}(g_\infty)\|\le C/\big((\prod_w \mathrm{archRoot}_1(w,g)\,\mathrm{archRoot}_2(w,g))^t(1+\mathrm{archRootSum}(g))^N\big)$ for all adelic $g$. (ii) $X.\mathrm{whittakerArch}$ satisfies the Whittaker law for `psiInf`. (iii) For every infinite idele $z$ and every $g$, $X.\mathrm{whittakerArch}(\mathrm{scalar}(z)g)=X.\mathrm{centralChar}(E z)\,X.\mathrm{whittakerArch}(g)$. (iv) For every admissible twist $\sigma$ of the ideles of $\mathbb Q$, every $t\in\mathbb C$ and $e\in\mathbb Z$ such that $\sigma$ has archimedean component of type $(t,e)$ at every real place of $\mathbb Q$, and every $g_\infty$, there exists an entire function $P$ on $\mathbb C$ such that: there is $\sigma_0$ with `IsArchZeta30ConvergentAbove` for $\nu_{\mathrm{mul}}$, the right translate $h\mapsto X.\mathrm{whittakerArch}(h\,g_\infty)$, the twist $\sigma\circ E$, base point $1$ and abscissa $\sigma_0$, and for $\mathrm{Re}\,s>\sigma_0$ the integral `archZeta30` equals $P(s)$ times the archimedean factor of the $L$-datum `heckeDatum K μ` with parameters $(uR+t,\ aR+e,\ uC+t,\ kC)$; $P$ is of at most exponential growth in vertical strips; in each vertical strip and for each $N$ the product $P(s)$ times that archimedean factor decays faster than $|\mathrm{Im}\,s|^{-N}$ for $|\mathrm{Im}\,s|$ large; and there is $\sigma_1$ with `IsArchZeta31ConvergentAbove` for $\nu_{\mathrm{mul}},\nu_{\mathrm{add}}$, the function `dualWhittakerFn3` of that right translate, the twist $(\sigma\circ E)^{-1}$, base point `weylPrime3 * transposeInv3 1` and abscissa $\sigma_1$, such that for $\mathrm{Re}(1-s)>\sigma_1$ the dual integral `archZetaDual31` at $1-s$ and base point $1$ equals the product of the root-number constant $\big(\prod_{w\ \mathrm{real}}\mathrm{signEpsilon}(aR_w+e)\big)\big(\prod_{w\ \mathrm{complex}} i^{|kC_w|}\big)\prod_{w}\mathrm{lambdaArch}(K,w)$, the factor $X.\mathrm{centralChar}(E a_\infty)\,\sigma(E a_\infty)^3$, the factor $|a|^{3(s-1/2)}$, the value $P(s)$, and the dual archimedean factor of the same Hecke datum at $1-s$. (v) There exist an admissible twist $\sigma$ of the ideles of $\mathbb Q$ and $s\in\mathbb C$ with `archZeta30` $\nu_{\mathrm{mul}}$, $X.\mathrm{whittakerArch}$, $\sigma\circ E$ at $s$ and base point $1$ non-zero.
--
--   Conclusion. For every $g_A\in\mathrm{GL}_3$ of the infinite adeles of $\mathbb Q$ there exists $\sigma_1\in\mathbb R$ such that `IsArchZeta31ConvergentAbove` holds for $\nu_{\mathrm{mul}}$, $\nu_{\mathrm{add}}$, the function `dualWhittakerFn3 X.whittakerArch`, i.e. $h\mapsto X.\mathrm{whittakerArch}(\mathrm{longWeyl}_3\cdot{}^{t}h^{-1})$, the trivial twist $1$, the base point $g_A$ and the abscissa $\sigma_1$: that is, for every $s$ with $\sigma_1<\mathrm{Re}\,s$ the function
--   $$(a,x)\longmapsto X.\mathrm{whittakerArch}\big(\mathrm{longWeyl}_3\cdot{}^{t}(\iota(\mathrm{diag}(a,1))\,n_{21}(x)\,g_A)^{-1}\big)\cdot\|a\|^{s-1}$$
--   is integrable on the product of the unit group and the additive group of the infinite adeles with respect to $\nu_{\mathrm{mul}}\times\nu_{\mathrm{add}}$, where $\iota$ is the embedding of $\mathrm{GL}_2$ in the upper left corner of $\mathrm{GL}_3$ and $n_{21}(x)$ is the corresponding lower unipotent element. Compared with the dual convergence clause inside `hArch`, the twist here is trivial rather than $(\sigma\circ E)^{-1}$ and the base point is arbitrary rather than `weylPrime3 * transposeInv3 1`.
--
--   This is the archimedean half of the convergence input for the dual $\mathrm{GL}_3\times\mathrm{GL}_1$ zeta integral in the converse-theorem argument for cubic induction: the dual convergence clause of the archimedean package, at the trivial twist and with the base point moved to an arbitrary element of $\mathrm{GL}_3$ of the infinite adeles. It is used by [`LanglandsTunnell.CubicInduction.sPartDual_integrable_of_isCubicInductionDataOn_of_isGaugeMajorised3`](thm.html#LanglandsTunnell.CubicInduction.sPartDual_integrable_of_isCubicInductionDataOn_of_isGaugeMajorised3) to obtain integrability of the dual $S$-part.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_isArchZeta31ConvergentAbove_dualWhittakerFn3_whittakerArch_of_isCubicInductionDataOn.lean

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

open scoped Classical in

theorem LanglandsTunnell.CubicInduction.exists_isArchZeta31ConvergentAbove_dualWhittakerFn3_whittakerArch_of_isCubicInductionDataOn
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
    ∀ gA : GL (Fin 3) (InfiniteAdeleRing ℚ), ∃ σ₁ : ℝ,
      IsArchZeta31ConvergentAbove ν_mul ν_add (dualWhittakerFn3 X.whittakerArch)
        (1 : (InfiniteAdeleRing ℚ)ˣ →* ℂˣ) gA σ₁ := by sorry
