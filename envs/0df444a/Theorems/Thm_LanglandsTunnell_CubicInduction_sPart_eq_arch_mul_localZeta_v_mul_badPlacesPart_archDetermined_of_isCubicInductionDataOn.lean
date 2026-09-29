-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_sPart_eq_arch_mul_localZeta_v_mul_badPlacesPart_archDetermined_of_isCubicInductionDataOn
-- name    : LanglandsTunnell.CubicInduction.sPart_eq_arch_mul_localZeta_v_mul_badPlacesPart_archDetermined_of_isCubicInductionDataOn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/d97bb934-84f0-5ca5-9513-8d4306a9fad5
-- title:
--   S-part factorisation of a GL₃ zeta integral
-- statement:
--   Fix a number field $K$ integral over $\mathbb{Q}$ (through an algebra structure $\mathcal{O}_\mathbb{Q}\to\mathcal{O}_K$), an additive character $\psi$ of $\mathbb{A}_\mathbb{Q}$, a character $\mu$ of $\mathbb{A}_K^\times$, and carrier data for $GL_2/\mathbb{Q}$ consisting of a set $D$, a level assignment $U$, Hecke generators `gen`, assembled by `productionPinsOf` into pins with the Borel structure and adelic Haar measure on $GL_2(\mathbb{A}_\mathbb{Q})$, full central subgroup, and the adelic additive Haar measure conditioned on the adelic box. Let $X$ be cubic induction data — a function `form` on $GL_3(\mathbb{A}_\mathbb{Q})$, a global Whittaker function `whittaker`, local Whittaker functions `whittakerLoc` $v$, an archimedean Whittaker function `whittakerArch`, a central character, and a dual Whittaker function — and assume `IsCubicInductionDataOn K pins ψ μ {v | IsBadPlace K μ v} X`: automorphy under $GL_3(\mathbb{Q})$, the central character law with an idele class character, cuspidality along the two radicals $P_{21}$, $P_{12}$, identification of `whittaker` with the $\psi$-Whittaker integral of `form` and of `dualWhittaker` with the $\psi^{-1}$-integral of the dual form, the $\psi$-Whittaker transformation laws, the mirabolic Whittaker expansions of `form` and its dual, factorisation of `whittaker` as the archimedean factor times the local factors over any finite set containing the bad places, sphericality with Hecke eigenvalues given by the induced coefficients of $\mu$ and level invariance at good places, multiplicity one locally, moderate growth, $K$-finiteness, and the moment and half-plane integrability conditions (summarised here). Let $S$ be a finite set of finite places of $\mathbb{Q}$ consisting exactly of the places $w$ with `IsBadPlace K μ w` ($w$ ramified in $K$, or $\mu$ ramified above $w$), and assume two integrability hypotheses: for every admissible twist $\tau$ (an idele class character that is continuous and unitary) and every $g\in GL_3(\mathbb{A}_\mathbb{Q})$ the integrand $a\mapsto W_X(\iota(\mathrm{diag}(a,1))g)\,\tau(a)\,\|a\|^{s-1}$, and the corresponding integrand built from the archimedean and local dual Whittaker integrals over the lower unipotent $n^-_{21}$, are integrable against the $S$-part measure $\nu_S$ of `productMeasureData ℚ S` on a right half-plane. Fix $v\in S$, a homomorphism $E$ from the infinite idele units to the idele units splitting the infinite part with trivial finite part, and a Haar measure $\nu_{\mathrm{mul}}$ on $(\mathbb{A}_{\mathbb{Q},\infty})^\times$ for a Borel measurable structure. Then there is a nonzero $c_S\in\mathbb{C}$ and a function $A^{\mathrm{d}}(g,s)$ depending on $g$ only through its archimedean component such that, for every admissible twist $\tau$ whose archimedean component at every real place is of type $(0,0)$ and every $g$ lying in the local maximal compact subgroup of $GL_3$ at all places outside $S$, there is $\sigma_0$ with: for $\mathrm{Re}\,s>\sigma_0$, the global $S$-part zeta integral $\int W_X(\iota(\mathrm{diag}(a,1))g)\tau(a)\|a\|^{s-1}\,d\nu_S(a)$ equals $c_S$ times the archimedean integral `archZeta30` of $h\mapsto W_{X,\infty}(h\,g_\infty)$ with trivial character at $s$ and identity argument, times `localZeta30` at $v$, times the product of `localZeta30` over $w\in S\setminus\{v\}$, each local factor formed from `X.whittakerLoc` $w$, the character `localChar τ w`, the argument $g_w$, and the multiplicative measure attached to the self-dual Haar measure at $w$; and, under the same hypotheses, the corresponding dual integral equals $c_S\,A^{\mathrm{d}}(g,s)$ times the factors `localZeta31` at $v$ and at the $w\in S\setminus\{v\}$, each normalised by the inverse of the self-dual measure of the local integers.
--
--   This is the unfolding of a global $GL_3$ zeta integral over the $S$-part of the ideles into an archimedean factor and local zeta integrals at the bad places, in the form in which the archimedean factor of the standard integral is identified with `archZeta30` while the archimedean factor of the dual integral is only pinned down as a function of the archimedean component of the test vector. It is the step that isolates a single bad place $v$, so that a local functional equation there can be inserted; it is used in the derivation of the global functional equations for the cubic induction data entering the converse theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_sPart_eq_arch_mul_localZeta_v_mul_badPlacesPart_archDetermined_of_isCubicInductionDataOn.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal MeasureTheory LanglandsTunnell.RankinSelberg

open scoped Classical in
attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in

theorem LanglandsTunnell.CubicInduction.sPart_eq_arch_mul_localZeta_v_mul_badPlacesPart_archDetermined_of_isCubicInductionDataOn
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ {v | IsBadPlace K μ v} X)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSbad : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w ↔ w ∈ S)
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
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ∈ S)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ, M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure] :
    ∃ cS : ℂ, cS ≠ 0 ∧ ∃ Ad : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ → ℂ,
      (∀ g g' : AdelicGL 3 (𝓞 ℚ) ℚ, archComponent3 (𝓞 ℚ) ℚ g = archComponent3 (𝓞 ℚ) ℚ g' →
        ∀ s : ℂ, Ad g s = Ad g' s) ∧
      (∀ τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ τ →
        (∀ w : InfinitePlace ℚ, w.IsReal → IsArchCompAt ℚ τ w 0 0) → ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ w : HeightOneSpectrum (𝓞 ℚ), w ∉ S →
          componentAt3 (𝓞 ℚ) ℚ w g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ w) →
        ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
          (∫ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
              X.whittaker (iotaGL (diagUnitGL2 a) * g) * ((τ a : ℂˣ) : ℂ) *
                ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1)
              ∂(NumberField.Idele.productMeasureData ℚ S).νS) =
            cS *
              archZeta30 ν_mul (fun h => X.whittakerArch (h * archComponent3 (𝓞 ℚ) ℚ g)) 1 s 1 *
              (letI := LanglandsTunnell.TateLocal.localBorel ℚ v
               localZeta30 v (Measure.comap Units.val
                  (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v)))
                (X.whittakerLoc v) (localChar τ v) s (componentAt3 (𝓞 ℚ) ℚ v g)) *
              ∏ w ∈ S.erase v,
                (letI := LanglandsTunnell.TateLocal.localBorel ℚ w
                 localZeta30 w (Measure.comap Units.val
                  (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ w)))
                  (X.whittakerLoc w) (localChar τ w) s (componentAt3 (𝓞 ℚ) ℚ w g))) ∧
      ∀ τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ τ →
        (∀ w : InfinitePlace ℚ, w.IsReal → IsArchCompAt ℚ τ w 0 0) → ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ w : HeightOneSpectrum (𝓞 ℚ), w ∉ S →
          componentAt3 (𝓞 ℚ) ℚ w g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ w) →
        ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
          (∫ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
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
            ((τ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1)
              ∂(NumberField.Idele.productMeasureData ℚ S).νS) =
            cS * Ad g s *
              (letI := LanglandsTunnell.TateLocal.localBorel ℚ v
               ((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set
                 (v.adicCompletion ℚ)) : ℂ)⁻¹ *
                 localZeta31 v (Measure.comap Units.val
                  (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v)))
                  (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v) (dualWhittakerFn3 (X.whittakerLoc v))
                  (localChar τ v) s (componentAt3 (𝓞 ℚ) ℚ v g)) *
              ∏ w ∈ S.erase v,
                (letI := LanglandsTunnell.TateLocal.localBorel ℚ w
                 ((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ w).real (w.adicCompletionIntegers ℚ : Set
                   (w.adicCompletion ℚ)) : ℂ)⁻¹ *
                   localZeta31 w (Measure.comap Units.val
                  (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ w)))
                    (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ w) (dualWhittakerFn3 (X.whittakerLoc w))
                    (localChar τ w) s (componentAt3 (𝓞 ℚ) ℚ w g)) := by sorry
