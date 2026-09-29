-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_sPart_eq_arch_mul_localZeta_v_mul_badPlacesPart_archTwisted_of_isCubicInductionDataOn
-- name    : LanglandsTunnell.CubicInduction.sPart_eq_arch_mul_localZeta_v_mul_badPlacesPart_archTwisted_of_isCubicInductionDataOn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/98f67a09-10c3-5929-bb04-61b1c23c4d0f
-- title:
--   Euler factorisation of the S-part zeta integral at v
-- statement:
--   Let $K$ be a number field whose ring of integers is an integral $\mathcal{O}_{\mathbb{Q}}$-algebra, let $\psi$ be an additive character of $\mathbb{A}_{\mathbb{Q}}$, $\mu$ a character of the idele group of $K$, $D\subseteq GL_2(\mathbb{A}_{\mathbb{Q}})$, $U$ an assignment of subgroups of $GL_2(\mathbb{A}_{\mathbb{Q}})$ to ideals of $\mathcal{O}_{\mathbb{Q}}$ and $gen$ an assignment of elements of $GL_2(\mathbb{A}_{\mathbb{Q}})$ to finite places. Let $X$ be cubic induction data (a function `form` on $GL_3(\mathbb{A}_{\mathbb{Q}})$ together with global, local and archimedean Whittaker functions, a central character and a dual Whittaker function), assumed via `IsCubicInductionDataOn` to satisfy the cubic-induction axioms — automorphy, central character, cuspidality along the two maximal parabolics, the Whittaker integral and its transformation law, the mirabolic expansion, factorisation over places, sphericity and $K_1$-level invariance outside the exceptional set, local multiplicity one, moderate growth, $K$-finiteness, the moment and half-plane integrability conditions, and the dual counterparts — relative to the carrier data `productionPinsOf` built from $D$, $U$, $gen$ and the adelic box (Borel structures, adelic Haar measure on $GL_2$, full central subgroup, and the additive adelic Haar measure conditioned on the box), the character $\psi$, and the set of places $v$ that either ramify in $K$ or lie below a prime where $\mu$ is ramified. Let $S$ be a finite set of finite places which is exactly this set of bad places, and $v\in S$. Assume that for every admissible twist $\tau$ (an idele class character of $\mathbb{Q}$, continuous and unitary) and every $g\in GL_3(\mathbb{A}_{\mathbb{Q}})$ both the direct integrand $a\mapsto W_X(\iota(\mathrm{diag}(a,1))g)\tau(a)\|a\|^{s-1}$ and its dual analogue (the archimedean and $S$-local integrals of the Weyl-transposed Whittaker functions against the self-dual Haar measures, normalised by the inverse volume of the local integers) are integrable for $\mathrm{Re}\,s$ large with respect to the $S$-part measure `(productMeasureData ℚ S).νS`. Let $E$ be a homomorphism from the infinite idele units to the idele units with infinite part the identity and trivial finite part, and $\nu_{\mathrm{mul}}$ a Haar measure on the infinite idele units. Then there exists $c_S\neq 0$ such that for every admissible twist $\tau$ — with no condition on its archimedean component — and every $g$ whose components outside $S$ lie in the local maximal compact subgroups (all entries of the component and its inverse of valuation $\le 1$), and for $\mathrm{Re}\,s$ large: the $S$-part integral of the direct integrand equals $c_S$ times `archZeta30` of the archimedean Whittaker function right-translated by $g_\infty$ with character $\tau\circ E$, times `localZeta30` at $v$, times the product of `localZeta30` over $w\in S\setminus\{v\}$, each formed with `X.whittakerLoc`, the character `localChar τ w` and the multiplicative measure attached to the self-dual Haar measure; and correspondingly the $S$-part integral of the dual integrand equals $c_S$ times `archZeta30` of the $y$-integrated dual archimedean Whittaker function with character $\tau\circ E$, times the products over $v$ and over $w\in S\setminus\{v\}$ of the volume-normalised factors `localZeta31` formed with `dualWhittakerFn3 (X.whittakerLoc w)`.
--
--   This is the Euler factorisation of the $S$-part of the global $GL_3$ zeta integral, in the form that singles out one chosen bad place $v$ and records the same factorisation for the dual (Weyl-transposed) integrand with the same constant $c_S$. It feeds the comparison of the global zeta integral with its local factors and, through that, the local functional equations and root-number identities used in the converse-theorem step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_sPart_eq_arch_mul_localZeta_v_mul_badPlacesPart_archTwisted_of_isCubicInductionDataOn.lean

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

theorem LanglandsTunnell.CubicInduction.sPart_eq_arch_mul_localZeta_v_mul_badPlacesPart_archTwisted_of_isCubicInductionDataOn
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
    ∃ cS : ℂ, cS ≠ 0 ∧
      (∀ τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ τ →
        ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ w : HeightOneSpectrum (𝓞 ℚ), w ∉ S →
          componentAt3 (𝓞 ℚ) ℚ w g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ w) →
        ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
          (∫ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
              X.whittaker (iotaGL (diagUnitGL2 a) * g) * ((τ a : ℂˣ) : ℂ) *
                ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1)
              ∂(NumberField.Idele.productMeasureData ℚ S).νS) =
            cS *
              archZeta30 ν_mul (fun h => X.whittakerArch (h * archComponent3 (𝓞 ℚ) ℚ g)) (τ.comp E) s 1 *
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
        ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
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
            cS *
              archZeta30 ν_mul (fun h => ∫ y : mixedEmbedding.mixedSpace ℚ,
                dualWhittakerFn3 X.whittakerArch (h *
                  lowerUnipotent21 ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y) * archComponent3 (𝓞 ℚ) ℚ g))
                (τ.comp E) s 1 *
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
