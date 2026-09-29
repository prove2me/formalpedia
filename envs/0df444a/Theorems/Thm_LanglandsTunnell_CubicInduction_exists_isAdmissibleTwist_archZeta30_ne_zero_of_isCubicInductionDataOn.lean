-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_archZeta30_ne_zero_of_isCubicInductionDataOn
-- name    : LanglandsTunnell.CubicInduction.exists_isAdmissibleTwist_archZeta30_ne_zero_of_isCubicInductionDataOn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/96fbf330-4446-50ad-8a95-2340e3a73247
-- title:
--   Archimedean zeta non-vanishing far right for a suitable translate
-- statement:
--   Setting. Let $K$ be a number field with an $\mathcal{O}_{\mathbb{Q}}$-algebra structure on $\mathcal{O}_K$ making $\mathcal{O}_K$ integral over $\mathcal{O}_{\mathbb{Q}}$, and assume $[K:\mathbb{Q}]=3$ (`hdeg`). Let $\psi$ be an additive character of the adele ring of $\mathbb{Q}$ which is global in the sense of `IsGlobalAddChar`: trivial on the image of $\mathbb{Q}$, continuous and non-trivial (`hψ`). Let $\mu$ be a character of the idele group of $K$ with values in $\mathbb{C}^\times$ which is an admissible twist (`hμ`), i.e. trivial on principal ideles $K^\times$, continuous and unitary.
--
--   Archimedean parameters of $\mu$. Functions $uR,aR$ on the real places and $uC,kC$ on the complex places of $K$ are given, with values in $\mathbb{C}$, $\mathbb{Z}/2$, $\mathbb{C}$, $\mathbb{Z}$ respectively, such that at each real place $w$ the local archimedean component of $\mu$ is $x\mapsto |x|^{\mathrm{mult}(w)\,uR_w}\,(\iota_w(x)/|x|)^{(aR_w)^{\mathrm{val}}}$ (`huR`) and at each complex place $w$ it is $x\mapsto |x|^{\mathrm{mult}(w)\,uC_w}\,(\iota_w(x)/|x|)^{kC_w}$ (`huC`), in the sense of `IsArchCompAt`.
--
--   Normalisations and non-base-change. For every finite place $v$ of $\mathbb{Q}$ the local component $\psi_v=$ `psiLoc ψ v` has `addCharLevel` equal to $0$ (`hlev`). The hypothesis `hns` asserts that $\mu$ is not obtained from $\mathbb{Q}$: there is no admissible twist $\eta$ of $\mathbb{Q}$ such that for every prime $\mathfrak{P}$ of $\mathcal{O}_K$ at which $\mu$ is unramified and whose prime $v$ below has $\eta$ unramified, $\mu$ of the uniformizer idele at $\mathfrak{P}$ equals $\eta$ of the uniformizer idele at $v$ raised to the inertia degree $f(\mathfrak{P}/v)$.
--
--   Carrier data and the cubic induction datum. A set $D$ of adelic $\mathrm{GL}_2$-matrices, a family $U$ of subgroups indexed by ideals of $\mathcal{O}_{\mathbb{Q}}$ and a family `gen` of adelic $\mathrm{GL}_2$-elements indexed by the finite places assemble, via `productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)`, into carrier pins over $\mathbb{Q}$ (Borel structure and adelic Haar measure on $\mathrm{GL}_2$, central subgroup $\top$, and the additive measure conditioned on the adelic box). A finite set $S$ of finite places of $\mathbb{Q}$ is assumed (`hS`) to consist exactly of the bad places of $(K,\mu)$, i.e. those $v$ ramified in $K$ or with $\mu$ ramified above $v$. Finally $X$ is a `CubicInductionData`, that is a tuple $(\mathrm{form},\mathrm{whittaker},(\mathrm{whittakerLoc}_v)_v,\mathrm{whittakerArch},\mathrm{centralChar},\mathrm{dualWhittaker})$, and `hX` asserts `IsCubicInductionDataOn` for $K$, these pins, $\psi$, $\mu$ and $S$: $X.\mathrm{form}$ is left invariant under $\mathrm{GL}_3(\mathbb{Q})$ and transforms under central ideles by $X.\mathrm{centralChar}$, which is trivial on principal ideles; $X.\mathrm{form}$ is cuspidal along both maximal parabolics $P_{21}$, $P_{12}$ of the pins; $X.\mathrm{whittaker}$ is the $\psi$-Whittaker integral of $X.\mathrm{form}$ and satisfies the $\psi$-Whittaker law $W(u(x,y,z)g)=\psi(x+y)W(g)$, with the mirabolic expansion summing to $X.\mathrm{form}$; each $X.\mathrm{whittakerLoc}_v$ satisfies the $\psi_v$-Whittaker law and has local multiplicity one; $X.\mathrm{whittaker}$ factorises as $X.\mathrm{whittakerArch}$ of the archimedean component times the product of the local factors over any finite set $T\supseteq S$ outside which the components lie in the local maximal compact; off $S$ the local factors are spherical of the type induced from $\mu$ and, at places unramified in $K$, invariant under the congruence subgroup of level `inducedLevelAt K μ v`; $X.\mathrm{form}$ has moderate growth, $X.\mathrm{whittakerArch}$ is $K_\infty$-finite, and $X.\mathrm{form}$ has iota moments and $X.\mathrm{whittaker}$ a Whittaker half-plane; and the same for the dual data, $X.\mathrm{dualWhittaker}$ being the $\psi^{-1}$-Whittaker integral of the dual form, with its Whittaker law, mirabolic expansion, iota moments and half-plane.
--
--   Global regularity hypotheses. $X.\mathrm{form}$, $X.\mathrm{whittaker}$ and $X.\mathrm{dualWhittaker}$ are continuous (`hcont`, `hcontW`, `hcontW'`); $X.\mathrm{whittaker}$ and $X.\mathrm{dualWhittaker}$ are gauge-majorised (`hW`, `hW'`), i.e. for each there are $t\in\mathbb{N}$, a finite set $T$ of finite places and $B\in\mathbb{R}$ such that the function vanishes outside the root level determined by $T,B$ and, for every $N$, is bounded there by $C/(\mathrm{rootSizeProd}(g)^t(1+\mathrm{archRootSum}(g))^N)$; and $X.\mathrm{whittakerArch}\neq 0$ (`hne`).
--
--   Local hypotheses at $S$ and a conductor bound. For each $v\in S$ (`hatS`): $X.\mathrm{whittakerLoc}_v(1)=1$; every non-zero element $F$ of the cyclic subspace generated by the right translates of $X.\mathrm{whittakerLoc}_v$ generates $X.\mathrm{whittakerLoc}_v$ back; $X.\mathrm{whittakerLoc}_v$ is right invariant under some open subgroup; and for every open subgroup $U_w$ of the local $\mathrm{GL}_3$ there is a finite family $B$ of functions spanning all $U_w$-invariant elements of that cyclic subspace. For each $v\in S$ (`hcent`): the local component `localChar X.centralChar v` is unitary, and $X.\mathrm{whittakerLoc}_v(\mathrm{scalar}(t)h)=$ `localChar X.centralChar v t` $\cdot X.\mathrm{whittakerLoc}_v(h)$. For every finite place $v$ of $\mathbb{Q}$ unramified in $K$ (`hωcond`), the local central character `localChar X.centralChar v` has some conductor exponent $a\le$ `inducedLevelAt K μ v`.
--
--   Archimedean normalisations. A monoid homomorphism $E$ from the infinite idele units into the idele units of $\mathbb{Q}$ splits the infinite part: $\mathrm{infPart}(E u)=u$ and $\mathrm{finPart}(E u)=1$ (`hE`). A non-zero rational $a$ is given (`ha`) together with the infinite idele unit $a_\infty$ whose underlying element is the image of $a$ (`haInf`), and the archimedean character $\psi_\infty$ with $\psi_\infty(x)=\mathrm{psiArch}(a x)$ (`hpsiInf`), which is the restriction of $\psi$ to the infinite adeles (`hψinf`). The additive measure $\nu_{\mathrm{add}}$ is $|a|^{1/2}$ times the transport of Lebesgue measure along the inverse of the mixed-space ring equivalence (`hν_add`), and $\nu_{\mathrm{mul}}$ is a Haar measure on the infinite idele units.
--
--   The archimedean package `hArch`. It consists of five groups of assertions. (i) $X.\mathrm{whittakerArch}$ is continuous and there is $t\in\mathbb{N}$ such that for every $N$ there is $C$ with $\|X.\mathrm{whittakerArch}(\mathrm{archComponent}_3 g)\|\le C/\big((\prod_w \mathrm{archRoot}_1(w,g)\,\mathrm{archRoot}_2(w,g))^t (1+\mathrm{archRootSum}(g))^N\big)$. (ii) $X.\mathrm{whittakerArch}$ satisfies the $\psi_\infty$-Whittaker law. (iii) For central $z$, $X.\mathrm{whittakerArch}(\mathrm{scalar}(z)g)=X.\mathrm{centralChar}(E z)\,X.\mathrm{whittakerArch}(g)$. (iv) For every admissible twist $\sigma$ of $\mathbb{Q}$, every $t\in\mathbb{C}$ and $e\in\mathbb{Z}$ with `IsArchCompAt ℚ σ w t e` at all real places $w$ of $\mathbb{Q}$, and every $g_\infty\in\mathrm{GL}_3$ of the infinite adeles, there is a function $P:\mathbb{C}\to\mathbb{C}$, differentiable on all of $\mathbb{C}$, such that: there is $\sigma_0$ beyond which the defining integral $\mathrm{archZeta30}$ for the translate $h\mapsto X.\mathrm{whittakerArch}(h g_\infty)$ and the character $\sigma\circ E$ at $g=1$ converges, and for $\mathrm{Re}\,s>\sigma_0$ that integral equals $P(s)$ times the archimedean factor of the $L$-datum `heckeDatum K μ` with parameters $(uR+t,\;aR+e\bmod 2,\;uC+t,\;kC)$; $P$ is bounded in every vertical strip by $C\exp(A|\mathrm{Im}\,s|)$; for every strip and every $N$ the product of $P$ with that archimedean factor is $O(|\mathrm{Im}\,s|^{-N})$ high in the strip; and there is $\sigma_1$ beyond which the dual integral $\mathrm{archZeta31}$ for $\mathrm{dualWhittakerFn3}$ of the translate, the character $(\sigma\circ E)^{-1}$ and the element $\mathrm{weylPrime3}\cdot\mathrm{transposeInv3}(1)$ converges, together with the functional equation: for $\mathrm{Re}(1-s)>\sigma_1$, $\mathrm{archZetaDual31}$ of the translate and $\sigma\circ E$ at $1-s$, $g=1$, equals the product of the root-number constant $\big(\prod_{w\ \mathrm{real}}\mathrm{signEpsilon}(aR_w+e)\big)\big(\prod_{w\ \mathrm{complex}} i^{|kC_w|}\big)\prod_{w}\mathrm{lambdaArch}(K,w)$, the factor $X.\mathrm{centralChar}(E a_\infty)\,\sigma(E a_\infty)^3$, the power $|a|^{3(s-1/2)}$, $P(s)$, and the dual archimedean factor of the same $L$-datum at $1-s$. (v) There exist an admissible twist $\sigma$ of $\mathbb{Q}$ and $s\in\mathbb{C}$ with $\mathrm{archZeta30}\,\nu_{\mathrm{mul}}\,X.\mathrm{whittakerArch}\,(\sigma\circ E)\,s\,1\neq 0$.
--
--   Conclusion. Under these hypotheses there exist $g_\infty\in\mathrm{GL}_3$ of the infinite adeles of $\mathbb{Q}$ and a character $\sigma$ of the idele units of $\mathbb{Q}$ such that: $\sigma$ is an admissible twist of $\mathbb{Q}$; there are $t\in\mathbb{C}$ and $e\in\mathbb{Z}$ with `IsArchCompAt ℚ σ w t e` at every real place $w$ of $\mathbb{Q}$ and with $(-1)^e=1$, so that the archimedean exponent $e$ is even; and for every $\sigma_0\in\mathbb{R}$ there is $s\in\mathbb{C}$ with $\mathrm{Re}\,s>\sigma_0$ and
--   $$\mathrm{archZeta30}\ \nu_{\mathrm{mul}}\ \big(h\mapsto X.\mathrm{whittakerArch}(h g_\infty)\big)\ (\sigma\circ E)\ s\ 1\;\neq\;0 ,$$
--   that is, the archimedean zeta integral $\int W_\infty(\mathrm{diag}(a,1,1)g_\infty)\,\sigma(E a)\,\|a\|^{s-1}\,d\nu_{\mathrm{mul}}(a)$ is non-zero at points of arbitrarily large real part.
--
--   This is the archimedean non-vanishing input for the cubic induction: it upgrades a single non-vanishing value of the archimedean $\mathrm{GL}_3$ zeta integral to non-vanishing at points arbitrarily far to the right, for a suitable right translate of the archimedean Whittaker function and an even admissible twist of $\mathbb{Q}$. It is used by the local extraction and identification steps at the bad places, which need the archimedean factor to be invertible in a right half-plane before comparing local zeta integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_archZeta30_ne_zero_of_isCubicInductionDataOn.lean

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

theorem LanglandsTunnell.CubicInduction.exists_isAdmissibleTwist_archZeta30_ne_zero_of_isCubicInductionDataOn
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
    ∃ (gInf : GL (Fin 3) (InfiniteAdeleRing ℚ)) (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ), IsAdmissibleTwist ℚ σ ∧
      (∃ (t : ℂ) (e : ℤ), (∀ w : InfinitePlace ℚ, w.IsReal → IsArchCompAt ℚ σ w t e) ∧ (-1 : ℂ) ^ e = 1) ∧
      ∀ σ₀ : ℝ, ∃ s : ℂ, σ₀ < s.re ∧ archZeta30 ν_mul (fun h => X.whittakerArch (h * gInf)) (σ.comp E) s 1 ≠ 0 := by sorry
