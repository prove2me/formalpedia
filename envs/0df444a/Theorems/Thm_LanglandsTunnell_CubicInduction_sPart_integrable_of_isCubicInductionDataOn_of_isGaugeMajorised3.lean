-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_sPart_integrable_of_isCubicInductionDataOn_of_isGaugeMajorised3
-- name    : LanglandsTunnell.CubicInduction.sPart_integrable_of_isCubicInductionDataOn_of_isGaugeMajorised3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/71da0957-e2e4-5d02-8874-25e8e73c28c1
-- title:
--   Convergence of the S-part zeta integral for cubic induction data
-- statement:
--   Fix a number field $K$ of degree $3$ over $\mathbb{Q}$, with $\mathcal{O}_K$ an integral $\mathcal{O}_{\mathbb{Q}}$-algebra, a global additive character $\psi$ of the adeles of $\mathbb{Q}$ (i.e. $\psi$ is trivial on principal adeles, continuous and non-trivial) and a homomorphism $\mu \colon (\mathbb{A}_K)^{\times} \to \mathbb{C}^{\times}$ which is an admissible twist: trivial on $K^{\times}$, continuous and of absolute value $1$.
--
--   The archimedean data of $\mu$ are recorded by families $uR, aR$ at the real places and $uC, kC$ at the complex places, together with the hypotheses `huR` and `huC` asserting `IsArchCompAt` at every real place $w$ with exponents $(uR\,w, (aR\,w).\mathrm{val})$ and at every complex place $w$ with exponents $(uC\,w, kC\,w)$, i.e. the local component of $\mu$ at $w$ is $x \mapsto \|x\|^{\mathrm{mult}(w)\,u}\,(x/\|x\|)^{a}$ under the embedding of the completion. The hypothesis `hlev` asserts that the local additive character `psiLoc ψ v` has `addCharLevel` equal to $0$ at every finite place $v$ of $\mathbb{Q}$, and `hns` asserts that $\mu$ is not a base-change twist: there is no admissible twist $\eta$ of $\mathbb{Q}$ such that for every prime $\mathfrak{P}$ of $\mathcal{O}_K$ at which $\mu$ is unramified and with $\eta$ unramified at $\mathfrak{P} \cap \mathcal{O}_{\mathbb{Q}}$, the value of $\mu$ at a uniformiser idele at $\mathfrak{P}$ equals the value of $\eta$ at a uniformiser idele below, raised to the inertia degree $f(\mathfrak{P}/\mathfrak{P}\cap\mathcal{O}_{\mathbb{Q}})$.
--
--   The carrier data consist of a set $D$ of adelic $\mathrm{GL}_2$-matrices, a family $U$ of subgroups indexed by ideals of $\mathcal{O}_{\mathbb{Q}}$, a family `gen` of adelic $\mathrm{GL}_2$-elements indexed by finite places, and a finite set $S$ of finite places of $\mathbb{Q}$ which, by `hS`, consists exactly of the bad places of $\mu$ (those ramified in $K$ or twist-ramified above). Finally $X$ is a `CubicInductionData`, that is a tuple $(\text{form}, \text{whittaker}, (\text{whittakerLoc}\,v)_v, \text{whittakerArch}, \text{centralChar}, \text{dualWhittaker})$, and `hX` asserts `IsCubicInductionDataOn` for $K$, the production pins built from $D$, $U$, `gen` and the adelic box, the character $\psi$, the character $\mu$ and the set $S$: the form is left invariant under the global points of $\mathrm{GL}_3(\mathbb{Q})$, transforms under central scalars by `centralChar` (an idele class character), is cuspidal along both parabolics $P_{21}$ and $P_{12}$, its $\psi$-Whittaker transform is `whittaker` which satisfies the $\psi$-Whittaker law for upper unipotents and whose mirabolic translates sum to the form; the local Whittaker functions satisfy the `psiLoc ψ v`-Whittaker law, the factorisation of `whittaker` into `whittakerArch` times the finite product of local factors over any finite set containing $S$ and outside which the components are integral, sphericity of the induced type off $S$, level invariance off $S$ at places unramified in $K$, local multiplicity one, moderate growth of the form, $K$-finiteness of `whittakerArch`, iota moments, the Whittaker half-plane property, and the corresponding clauses for `dualWhittaker` relative to $\psi^{-1}$ and the dual form.
--
--   The analytic hypotheses are: `hcont`, `hcontW`, `hcontW'`, continuity of `X.form`, `X.whittaker` and `X.dualWhittaker`; `hW` and `hW'`, that `X.whittaker` and `X.dualWhittaker` are gauge-majorised over $\mathbb{Q}$, i.e. there are $t$, a finite set $T$ of finite places and $B$ such that for every $N$ some constant $C$ bounds the function by $C/(\text{rootSizeProd}^{t}(1+\text{archRootSum})^{N})$ on the root level set, the function vanishing off it; `hne`, that `X.whittakerArch \neq 0`; `hatS` (four clauses), that at each $w \in S$ the local Whittaker function takes value $1$ at the identity, every non-zero member of its cyclic space generates it back, it is right invariant under some open subgroup, and for each open subgroup the invariants in its cyclic space lie in the span of a finite set; `hcent`, that at each $w \in S$ the local component of the central character is unitary and `whittakerLoc w` transforms by it under central scalars; `hωcond`, that at each finite place $v$ unramified in $K$ the local central character has a conductor exponent at most the induced level `inducedLevelAt K μ v`.
--
--   Further, $E$ is a monoid homomorphism from the infinite idele group to the full idele group splitting the infinite part, `hE` asserting that $E u$ has infinite part $u$ and trivial finite part; $a$ is a non-zero rational with $a_{\infty}$ the corresponding infinite idele (`haInf`) and `psiInf` the archimedean character $x \mapsto \mathrm{psiArch}(a x)$ (`hpsiInf`), which by `hψinf` is the restriction of $\psi$ to the infinite adeles; $\nu_{\mathrm{add}}$ is the measure $|a|^{1/2}$ times the pushforward of Lebesgue measure on the mixed space (`hν_add`), and $\nu_{\mathrm{mul}}$ a Haar measure on the infinite ideles.
--
--   The archimedean hypothesis `hArch` is a conjunction of five groups, summarised here: continuity of `X.whittakerArch` together with a uniform rapid-decay bound in the archimedean root coordinates; the $\mathrm{psiInf}$-Whittaker law for `X.whittakerArch`; the central transformation law of `X.whittakerArch` under scalars $z$ by `X.centralChar (E z)`; for every admissible twist $\sigma$ of $\mathbb{Q}$, every $(t,e)$ realising the real archimedean components of $\sigma$ and every $g_{\infty}$, the existence of an entire function $P$ such that the archimedean zeta integral `archZeta30` of the right translate of `X.whittakerArch` converges in a right half-plane and equals $P(s)$ times the archimedean factor of the Hecke datum `heckeDatum K μ` with parameters $uR+t$, $aR+e$, $uC+t$, $kC$, with vertical-strip bounds of exponential type on $P$ and rapid decay of the product in strips, and a functional equation expressing the dual integral `archZetaDual31` at $1-s$ as an explicit constant (a product of sign factors $\mathrm{signEpsilon}(aR+e)$ over real places of $K$, of powers of $i$ attached to $kC$ over the complex places, and of $\mathrm{lambdaArch}$ over all infinite places of $K$), times $\mathrm{centralChar}(E a_{\infty})\,\sigma(E a_{\infty})^{3}$, times $|a|^{3(s-1/2)}$, times $P(s)$, times the dual archimedean factor of the same Hecke datum at $1-s$; and the existence of some admissible twist $\sigma$ for which `archZeta30` of `X.whittakerArch` is non-zero at some $s$.
--
--   Under these hypotheses the conclusion is: for every admissible twist $\tau$ of $\mathbb{Q}$ and every $g \in \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ there exists $\sigma_0 \in \mathbb{R}$ such that for all $s$ with $\sigma_0 < \Re s$ the function
--   $$a \longmapsto X.\mathrm{whittaker}\bigl(\iota(\mathrm{diag}(a,1))\,g\bigr)\,\tau(a)\,\|a\|^{\,s-1}$$
--   on the idele group of $\mathbb{Q}$ is integrable with respect to the measure $\nu_S$ of [`NumberField.Idele.productMeasureData ℚ S`](def/NumberField_IdeleProductMeasure.html#L679), where $\|a\|$ is the idele norm `TateGlobal.ideleNorm ℚ` and $\iota$ is the embedding of $\mathrm{GL}_2$ into $\mathrm{GL}_3$ in the upper left block.
--
--   This is the convergence half of the Hecke-theoretic input to the converse theorem for $\mathrm{GL}_3$ used in the Langlands–Tunnell step: it asserts that the global zeta integral attached to the Whittaker function of cubic induction data, restricted to the $S$-part of the idele group, converges absolutely in a right half-plane. It is combined with its dual counterpart in [`LanglandsTunnell.CubicInduction.sPart_integrable_and_dual_of_isCubicInductionDataOn_of_isGaugeMajorised3`](thm.html#LanglandsTunnell.CubicInduction.sPart_integrable_and_dual_of_isCubicInductionDataOn_of_isGaugeMajorised3).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_sPart_integrable_of_isCubicInductionDataOn_of_isGaugeMajorised3.lean

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

theorem LanglandsTunnell.CubicInduction.sPart_integrable_of_isCubicInductionDataOn_of_isGaugeMajorised3
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
          X.whittaker (iotaGL (diagUnitGL2 a) * g) * ((τ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1))
          (NumberField.Idele.productMeasureData ℚ S).νS := by sorry
