-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_aestronglyMeasurable_sPartDual_integrand_of_isCubicInductionDataOn
-- name    : LanglandsTunnell.CubicInduction.aestronglyMeasurable_sPartDual_integrand_of_isCubicInductionDataOn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/ecadd5e7-e603-5060-a85d-5bb9b9e7760e
-- title:
--   Measurability of the dual S-part zeta integrands
-- statement:
--   Throughout, $K$ is a number field with $\mathcal{O}_{\mathbb{Q}}$-algebra structure on $\mathcal{O}_K$, integral over $\mathcal{O}_{\mathbb{Q}}$, and the hypothesis `hdeg` requires $[K:\mathbb{Q}]=3$.
--
--   **Global characters.** An additive character $\psi$ of the adele ring of $\mathbb{Q}$ is given, with `hψ` asserting that $\psi$ is trivial on the image of $\mathbb{Q}$, continuous and non-trivial, and `hlev` asserting that for every finite place $v$ the local component `psiLoc ψ v` (the restriction of $\psi$ along the embedding of $\mathbb{Q}_v$) has level $0$, i.e. the supremum of the integers $n$ such that $\psi$ kills $\{x : \mathrm{v}(x)\le \exp n\}$ is $0$. A homomorphism $\mu$ from the idele units of $K$ to $\mathbb{C}^\times$ is given, with `hμ` asserting that $\mu$ is an admissible twist: trivial on principal ideles, continuous and of absolute value $1$ everywhere.
--
--   **Archimedean type of $\mu$.** Families $uR, aR$ indexed by the real places and $uC, kC$ indexed by the complex places of $K$ are given, with values in $\mathbb{C}$, $\mathbb{Z}/2$, $\mathbb{C}$, $\mathbb{Z}$ respectively; `huR` and `huC` assert `IsArchCompAt K μ w` at each real place $w$ with parameters $(uR_w, (aR_w)^{\mathrm{val}})$ and at each complex place $w$ with parameters $(uC_w, kC_w)$, that is, the local component of $\mu$ at $w$ is $x \mapsto \lVert x\rVert^{\,\mathrm{mult}(w)\,u}\,\bigl(x/\lVert x\rVert\bigr)^{a}$.
--
--   **Non-base-change.** The hypothesis `hns` excludes the existence of an admissible twist $\eta$ of $\mathbb{Q}$ such that for every prime $\mathfrak{P}$ of $\mathcal{O}_K$ at which $\mu$ is unramified and whose prime $p$ of $\mathcal{O}_{\mathbb{Q}}$ below it is unramified for $\eta$, one has $\mu(\varpi_{\mathfrak{P}}) = \eta(\varpi_p)^{f}$, where $\varpi$ denotes the uniformiser idele and $f =$ `inertiaDeg'` of $\mathfrak{P}$ over $p$.
--
--   **Carrier data and the cubic induction datum.** A set $D$ of adelic $\mathrm{GL}_2$-points, a family $U$ of subgroups indexed by ideals of $\mathcal{O}_{\mathbb{Q}}$ and a family $\mathrm{gen}$ of adelic $\mathrm{GL}_2$-points indexed by the finite places are given, together with a finite set $S$ of finite places of $\mathbb{Q}$ which by `hS` is exactly the set of bad places, namely those $v$ ramified in $K$ or lying below a prime where $\mu$ is twist-ramified. A datum $X$ of type `CubicInductionData` consists of a form $X.\mathrm{form}$ on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$, its Whittaker function $X.\mathrm{whittaker}$, local Whittaker functions $X.\mathrm{whittakerLoc}\,v$ on $\mathrm{GL}_3(\mathbb{Q}_v)$, an archimedean Whittaker function $X.\mathrm{whittakerArch}$ on $\mathrm{GL}_3$ of the infinite adeles, a central character $X.\mathrm{centralChar}$, and a dual Whittaker function $X.\mathrm{dualWhittaker}$. The hypothesis `hX` asserts `IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ S X`, whose clauses (automorphy under $\mathrm{GL}_3(\mathbb{Q})$, central-character equivariance and idele-class property of $X.\mathrm{centralChar}$, cuspidality along the two maximal parabolics, the identification of $X.\mathrm{whittaker}$ with the $\psi$-Whittaker integral of $X.\mathrm{form}$ and its Whittaker transformation law, the mirabolic expansion, the local Whittaker laws for `psiLoc ψ v`, factorisation of $X.\mathrm{whittaker}$ as $X.\mathrm{whittakerArch}$ times a finite product of local factors over any finite set containing $S$ and off which the component lies in the maximal compact, sphericity of the induced type off $S$, invariance under the congruence subgroup of the induced level off $S$ at places unramified in $K$, local multiplicity one, moderate growth, $K$-finiteness of $X.\mathrm{whittakerArch}$, the iota-moment and Whittaker half-plane conditions, and the corresponding clauses for $\psi^{-1}$ and the dual form) are summarised here.
--
--   **Regularity and local conditions.** The hypotheses `hcont`, `hcontW`, `hcontW'` require continuity of $X.\mathrm{form}$, $X.\mathrm{whittaker}$ and $X.\mathrm{dualWhittaker}$; `hW` and `hW'` require $X.\mathrm{whittaker}$ and $X.\mathrm{dualWhittaker}$ to be gauge-majorised in the sense of `IsGaugeMajorised3` (vanishing outside a root-level region, with bounds $C/(\mathrm{rootSizeProd}^t(1+\mathrm{archRootSum})^N)$ inside it); `hne` requires $X.\mathrm{whittakerArch}\neq 0$. The hypothesis `hatS` requires, at each $w\in S$, four conditions on $W_w := X.\mathrm{whittakerLoc}\,w$: the normalisation $W_w(1)=1$; that every non-zero element of the cyclic subspace generated by $W_w$ under right translation generates $W_w$ back; that $W_w$ is right-invariant under some open subgroup; and that for every open subgroup $U_w$ the $U_w$-invariants of that cyclic subspace lie in the span of a finite set of functions. The hypothesis `hcent` requires, at each $w\in S$, that the local component of $X.\mathrm{centralChar}$ at $w$ be unitary and that $W_w$ transform under scalar matrices by that local character. The hypothesis `hωcond` requires, at each finite place $v$ unramified in $K$, that the local central character at $v$ have a conductor exponent $a \le$ `inducedLevelAt K μ v`.
--
--   **Archimedean normalisations.** A monoid homomorphism $E$ from the units of the infinite adeles to the idele units is given, with `hE` asserting that $E u$ has infinite part $u$ and trivial finite part. A non-zero rational $a$ is given together with an infinite idele $a_\infty$ whose underlying element is the image of $a$, and an archimedean additive character $\psi_\infty$ with $\psi_\infty(x) = \mathrm{psiArch}(a x)$ (`hpsiInf`), which by `hψinf` is the restriction of $\psi$ to the infinite component. Borel measurable structures on the infinite adeles and on their unit group are in force. The measure $\nu_{\mathrm{add}}$ is, by `hν_add`, $|a|^{1/2}$ times the transport of Lebesgue measure along the inverse of the ring equivalence with the mixed space of $\mathbb{Q}$, and $\nu_{\mathrm{mul}}$ is a Haar measure on the units of the infinite adeles.
--
--   **The archimedean package `hArch`.** This conjunction (summarised here) requires: continuity of $X.\mathrm{whittakerArch}$ together with decay bounds $\lVert X.\mathrm{whittakerArch}(g_\infty)\rVert \le C/\bigl((\prod_w \mathrm{archRoot}_1\,\mathrm{archRoot}_2)^t (1+\mathrm{archRootSum})^N\bigr)$; the $\psi_\infty$-Whittaker transformation law; scalar equivariance through $X.\mathrm{centralChar}\circ E$; for every admissible twist $\sigma$ of $\mathbb{Q}$, every pair $(t,e)\in\mathbb{C}\times\mathbb{Z}$ realising the archimedean components of $\sigma$ at the real places, and every $g_\infty$, the existence of an entire function $P$ together with a half-plane of convergence of the archimedean zeta integral `archZeta30` for $X.\mathrm{whittakerArch}(\cdot\, g_\infty)$ and the identity `archZeta30` $= P(s)\cdot \Gamma$-factor of `heckeDatum K μ (uR + t) (aR + e) (uC + t) kC`, vertical-strip bounds $\lVert P(s)\rVert \le C e^{A|\mathrm{Im}\,s|}$, rapid decay of the product in vertical strips, and convergence of the dual integral `archZetaDual31` together with its functional equation in which the factor $\bigl(\prod_{w \text{ real}} \mathrm{signEpsilon}(aR_w+e)\bigr)\bigl(\prod_{w \text{ complex}} i^{|kC_w|}\bigr)\bigl(\prod_w \mathrm{lambdaArch}\,w\bigr)$, the value $X.\mathrm{centralChar}(E a_\infty)\,\sigma(E a_\infty)^3$, the power $|a|^{3(s-1/2)}$, $P(s)$ and the dual $\Gamma$-factor of the same Hecke datum at $1-s$ occur; and finally the existence of an admissible twist $\sigma$ of $\mathbb{Q}$ and a point $s$ at which `archZeta30` of $X.\mathrm{whittakerArch}$ is non-zero.
--
--   **Conclusion.** For every homomorphism $\tau$ from the idele units of $\mathbb{Q}$ to $\mathbb{C}^\times$ that is an admissible twist (trivial on principal ideles, continuous, unitary), every $g \in \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ and every $s \in \mathbb{C}$, the following three measurability assertions hold. Write $\widetilde{W}(h) = W(w_{3}\cdot {}^{t}h^{-1})$ for the involution `dualWhittakerFn3` (with $w_3$ the long Weyl element and ${}^{t}h^{-1}$ the transpose of the inverse), $\iota$ for the embedding `iotaGL` of $\mathrm{GL}_2$ into the upper-left block of $\mathrm{GL}_3$, $\mathrm{diag}(x)$ for `diagUnitGL2` and $n^{-}(x)$ for the lower unipotent matrix `lowerUnipotent21 x`.
--
--   (1) The function of an idele unit $a$ given by the product of: the integral over the mixed space of $\mathbb{Q}$, in the variable $y$, of $\widetilde{X.\mathrm{whittakerArch}}$ evaluated at the archimedean component of $\iota(\mathrm{diag}(a))$ times $n^{-}$ of the image of $y$ under the inverse of the ring equivalence with the infinite adeles, times the archimedean component of $g$; the product over $v \in S$ of the reciprocal of the `selfDualHaarAt ℚ v`-volume of the integers of $\mathbb{Q}_v$, multiplied by the integral over $\mathbb{Q}_v$, with respect to `selfDualHaarAt ℚ v`, of the dual of $X.\mathrm{whittakerLoc}\,v$ at the component at $v$ of $\iota(\mathrm{diag}(a))$ times $n^{-}(x)$ times the component at $v$ of $g$; the value $\tau(a)$; and $\mathrm{ideleNorm}(a)^{s-1}$ — is almost everywhere strongly measurable for the measure `νS` of [`NumberField.Idele.productMeasureData ℚ S`](def/NumberField_IdeleProductMeasure.html#L679).
--
--   (2) The function of a unit $u$ of the infinite adeles given by the integral over the mixed space, in $y$, of $\widetilde{X.\mathrm{whittakerArch}}$ at $\iota(\mathrm{diag}(u))\,n^{-}(y)$ times the archimedean component of $g$, multiplied by $\lVert u\rVert^{s-1}$, is almost everywhere strongly measurable for $\nu_{\mathrm{mul}}$.
--
--   (3) For every $w \in S$, the function of $t \in \mathbb{Q}_w^\times$ given by the integral over $\mathbb{Q}_w$, with respect to `selfDualHaarAt ℚ w`, of the dual of $X.\mathrm{whittakerLoc}\,w$ at $\iota(\mathrm{diag}(t))\,n^{-}(x)$ times the component at $w$ of $g$, multiplied by $\mathrm{modulus}(t)^{s-1}$, is almost everywhere strongly measurable for the pullback along the inclusion of units of the multiplicative measure `mulMeasure (selfDualHaarAt ℚ w)`, that is of the measure $dx/|x|$ on $\mathbb{Q}_w \setminus \{0\}$.
--
--   The conclusion is a pure measurability statement: no integrability, no value of any of the three integrals is asserted. Among the facts used are the identity of the local module with the norm on an adic completion and the continuity of the idele norm.
--
--   A preparatory measurability step in the cubic-induction (Langlands–Tunnell) part of the development: the three integrands occurring in the dual $S$-part decomposition of the global $\mathrm{GL}_3\times\mathrm{GL}_1$ zeta integral — the archimedean one, the one over the units of the infinite adeles, and the local ones at the bad places — are almost everywhere strongly measurable for the relevant measures. It is the measurability half of the corresponding integrability statement [`LanglandsTunnell.CubicInduction.sPartDual_integrable_of_isCubicInductionDataOn_of_isGaugeMajorised3`](thm.html#LanglandsTunnell.CubicInduction.sPartDual_integrable_of_isCubicInductionDataOn_of_isGaugeMajorised3), which cites it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_aestronglyMeasurable_sPartDual_integrand_of_isCubicInductionDataOn.lean

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

theorem LanglandsTunnell.CubicInduction.aestronglyMeasurable_sPartDual_integrand_of_isCubicInductionDataOn
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
    ∀ τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ τ → ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (s : ℂ),
      AEStronglyMeasurable (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
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
        (NumberField.Idele.productMeasureData ℚ S).νS ∧
      AEStronglyMeasurable (fun u : (InfiniteAdeleRing ℚ)ˣ =>
          (∫ y : mixedEmbedding.mixedSpace ℚ,
              dualWhittakerFn3 X.whittakerArch (iotaGL (diagUnitGL2 u) *
                lowerUnipotent21 ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y) * archComponent3 (𝓞 ℚ) ℚ g)) *
            ((‖(u : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ) ^ (s - 1)) ν_mul ∧
      ∀ w ∈ S,
        letI := LanglandsTunnell.TateLocal.localBorel ℚ w
        AEStronglyMeasurable (fun t : (w.adicCompletion ℚ)ˣ =>
            (∫ x : w.adicCompletion ℚ,
                dualWhittakerFn3 (X.whittakerLoc w) (iotaGL (diagUnitGL2 t) * lowerUnipotent21 x *
                  componentAt3 (𝓞 ℚ) ℚ w g) ∂(LanglandsTunnell.TateLocal.selfDualHaarAt ℚ w)) *
              ((LanglandsTunnell.TateLocal.modulus (t : w.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1))
          (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ w))) := by sorry
