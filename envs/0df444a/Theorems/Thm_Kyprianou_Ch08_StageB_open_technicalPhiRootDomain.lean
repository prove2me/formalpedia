-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_open_technicalPhiRootDomain
-- name    : Kyprianou.Ch08.StageB.open_technicalPhiRootDomain
-- status  : Open
-- author  : @WillR
-- created : 2026-11-17T07:33:44.344936+00:00
-- url     : https://prove2.me/theorems/f5353e9b-0cac-4982-bd61-fd896d6fb219
-- title:
--   Technical bridge: technicalPhiRootDomain
-- statement:
--   Non-source Open technical dependency; never a proved import and never an extra hypothesis of the complete source result.
-- source:
--   Kyprianou (2006), exact original 382-page edition, SHA-256 3696f4b3373cabcd968e300994fdd70a04df97b57a16837ad672bac5a1c269bf; non-source technical child required for Kyprianou Chapter 8

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false
namespace Kyprianou.Ch08



structure ProcessData (Ω : Type*) [MeasurableSpace Ω] where
  law : Measure Ω
  probabilityLaw : IsProbabilityMeasure law
  X : ℝ≥0 → Ω → ℝ
  tripletA : ℝ
  gaussian : ℝ
  jumps : Measure ℝ


structure SpectrallyNegativeModel (Ω : Type*) [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] where
  X : ℝ≥0 → Ω → ℝ
  levy : ProbabilityTheory.IsLevyProcess X P
  triplet : ProbabilityTheory.LevyKhintchineTriple
  characteristic : ∀ (t : ℝ≥0) (ξ : ℝ),
    charFun (P.map (X t)) ξ =
      Complex.exp (((t : ℝ) : ℂ) *
        Kyprianou.Ch01.levyTripleExponent triplet ξ)
  negativeJumps : triplet.levyMeasure (Set.Ici (0 : ℝ)) = 0
  gaussianCoefficient : ℝ
  gaussianNonnegative : 0 ≤ gaussianCoefficient
  gaussianVarianceMatch :
    gaussianCoefficient ^ 2 = (triplet.gaussianVariance : ℝ)
  excludesNegativeSubordinator :
    ¬ (∀ᵐ ω ∂P, Antitone (fun t : ℝ≥0 => X t ω))


def HasCompletedNaturalFiltration {Ω : Type} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (F : Filtration ℝ≥0 m) : Prop :=
  Kyprianou.Ch03.IsCompletedNaturalFiltration P D.X F


noncomputable def SpectrallyNegativeModel.toData
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) : ProcessData Ω :=
  { law := P
    probabilityLaw := inferInstance
    X := D.X
    tripletA := D.triplet.drift
    gaussian := D.gaussianCoefficient
    jumps := D.triplet.levyMeasure }


def HasNegativeJumpSupport (jumpMeasure : Measure ℝ) : Prop :=
  jumpMeasure (Set.Ici (0 : ℝ)) = 0


def IsNegativeLevyMeasure (jumpMeasure : Measure ℝ) : Prop :=
  HasNegativeJumpSupport jumpMeasure ∧
  (∫⁻ x : ℝ, ENNReal.ofReal (min (x ^ 2) 1) ∂jumpMeasure) < ⊤


def HasStationaryIncrementLaws {Ω : Type*} [MeasurableSpace Ω]
    (D : ProcessData Ω) : Prop :=
  ∀ s t : ℝ≥0,
    Measure.map (fun ω => D.X (s + t) ω - D.X s ω) D.law =
    Measure.map (D.X t) D.law


noncomputable def tripletLaplace (a σ : ℝ) (jumpMeasure : Measure ℝ) (β : ℝ) : ℝ :=
  -a * β + σ ^ 2 * β ^ 2 / 2 +
    ∫ x : ℝ, (Real.exp (β * x) - 1 -
      (if -1 < x then β * x else 0)) ∂jumpMeasure


def IsLaplaceExponent {Ω : Type*} [MeasurableSpace Ω]
    (D : ProcessData Ω) (ψ : ℝ → ℝ) : Prop :=
  ∀ (β : ℝ) (t : ℝ≥0), 0 ≤ β → 0 < t →
    Integrable (fun ω => Real.exp (β * D.X t ω)) D.law ∧
    ψ β = Real.log (∫ ω, Real.exp (β * D.X t ω) ∂D.law) / (t : ℝ)


def IsFullMomentLaplaceExponent {Ω : Type*} [MeasurableSpace Ω]
    (D : ProcessData Ω) (ψ : ℝ → ℝ) : Prop :=
  IsLaplaceExponent D ψ ∧
  ∀ (c : ℝ) (t : ℝ≥0), 0 < t →
    Integrable (fun ω => Real.exp (c * D.X t ω)) D.law →
      0 < (∫ ω, Real.exp (c * D.X t ω) ∂D.law) ∧
      ψ c = Real.log
        (∫ ω, Real.exp (c * D.X t ω) ∂D.law) / (t : ℝ)


def HasLawfulEsscherMoment {Ω : Type*} [MeasurableSpace Ω]
    (D : ProcessData Ω) (ψ : ℝ → ℝ) (c : ℝ) : Prop :=
  IsFullMomentLaplaceExponent D ψ ∧
  Integrable (fun ω => Real.exp (c * D.X 1 ω)) D.law ∧
  0 < (∫ ω, Real.exp (c * D.X 1 ω) ∂D.law)


def HasLawfulEsscherDensities {Ω : Type*} [MeasurableSpace Ω]
    (D : ProcessData Ω) (ψ : ℝ → ℝ) (c : ℝ) : Prop :=
  HasLawfulEsscherMoment D ψ c ∧
  ∀ t : ℝ≥0, 0 < t →
    Integrable (fun ω => Real.exp (c * D.X t ω)) D.law ∧
    Integrable (fun ω => Real.exp
      (c * D.X t ω - ψ c * (t : ℝ))) D.law ∧
    (∀ ω, 0 < Real.exp
      (c * D.X t ω - ψ c * (t : ℝ))) ∧
    (∫ ω, Real.exp
      (c * D.X t ω - ψ c * (t : ℝ)) ∂D.law) = 1


def HasLawTripletLaplaceBridge {Ω : Type*} [MeasurableSpace Ω]
    (D : ProcessData Ω) : Prop :=
  IsNegativeLevyMeasure D.jumps ∧
  IsLaplaceExponent D (tripletLaplace D.tripletA D.gaussian D.jumps) ∧
  ∀ β : ℝ, 0 ≤ β →
    tripletLaplace D.tripletA D.gaussian D.jumps β =
      AvramDividend.Classical.laplaceExponent
        (-D.tripletA) D.gaussian D.jumps β


def HasPairwiseIndependentDisjointIncrements {Ω : Type*} [MeasurableSpace Ω]
    (D : ProcessData Ω) : Prop :=
  ∀ s t u v : ℝ≥0, s ≤ t → t ≤ u → u ≤ v →
    Measure.map
      (fun ω => (D.X t ω - D.X s ω, D.X v ω - D.X u ω)) D.law =
    (Measure.map (fun ω => D.X t ω - D.X s ω) D.law).prod
      (Measure.map (fun ω => D.X v ω - D.X u ω) D.law)


def RightRootSet (ψ : ℝ → ℝ) (q : ℝ) : Set ℝ :=
  {β | 0 ≤ β ∧ ψ β = q}


noncomputable def Phi (ψ : ℝ → ℝ) (q : ℝ) : ℝ :=
  sSup (RightRootSet ψ q)


def PhiIsLargestRoot (ψ : ℝ → ℝ) (q : ℝ) : Prop :=
  0 ≤ q ∧ (Phi ψ q ∈ RightRootSet ψ q) ∧
  ∀ β ∈ RightRootSet ψ q, β ≤ Phi ψ q


def HasBoundedVariationTriplet (σ : ℝ) (jumpMeasure : Measure ℝ) : Prop :=
  σ = 0 ∧
  (∫⁻ x in Set.Ioo (-1 : ℝ) 0, ENNReal.ofReal |x| ∂jumpMeasure) < ⊤


noncomputable def bvDrift (a : ℝ) (jumpMeasure : Measure ℝ) : ℝ :=
  -a - ∫ x in Set.Ioo (-1 : ℝ) 0, x ∂jumpMeasure


def HasPositiveBVDrift (a σ : ℝ) (jumpMeasure : Measure ℝ) : Prop :=
  HasBoundedVariationTriplet σ jumpMeasure ∧ 0 < bvDrift a jumpMeasure


noncomputable def bvLaplace (d : ℝ) (jumpMeasure : Measure ℝ) (β : ℝ) : ℝ :=
  d * β - ∫ x in Set.Iio (0 : ℝ),
    (1 - Real.exp (β * x)) ∂jumpMeasure


noncomputable def esscherDensity {Ω : Type*} [MeasurableSpace Ω]
    (D : ProcessData Ω) (ψ : ℝ → ℝ) (c : ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (c * D.X t ω - ψ c * (t : ℝ))


def IsEsscherParameter (c : ℝ) : Prop := 0 ≤ c


def shiftedExponent (ψ : ℝ → ℝ) (c beta : ℝ) : ℝ :=
  ψ (beta + c) - ψ c


noncomputable def esscherFiniteTimeLaw {Ω : Type*} [MeasurableSpace Ω]
    (D : ProcessData Ω) (ψ : ℝ → ℝ)
    (c : ℝ) (t : ℝ≥0) : Measure Ω :=
  D.law.withDensity (fun ω => ENNReal.ofReal
    (esscherDensity D ψ c t ω))



def IsQScale (ψ : ℝ → ℝ) (q : ℝ) (W : ℝ → ℝ) : Prop :=
  PhiIsLargestRoot ψ q ∧
  (∀ x : ℝ, x < 0 → W x = 0) ∧
  (∀ x : ℝ, 0 ≤ W x) ∧
  ContinuousOn W (Set.Ici (0 : ℝ)) ∧
  MonotoneOn W (Set.Ici (0 : ℝ)) ∧
  (∀ β : ℝ, 0 ≤ β → Phi ψ q < β →
    IntegrableOn (fun x : ℝ => Real.exp (-β * x) * W x)
      (Set.Ioi (0 : ℝ)) volume ∧
    (∫ x in Set.Ioi (0 : ℝ), Real.exp (-β * x) * W x ∂volume) =
      (ψ β - q)⁻¹)


def HasStrictQScale (ψ : ℝ → ℝ) (q : ℝ) (W : ℝ → ℝ) : Prop :=
  IsQScale ψ q W ∧ StrictMonoOn W (Set.Ici (0 : ℝ))


def IsScaleTransformDomainBridge (ψ : ℝ → ℝ) (q : ℝ) : Prop :=
  PhiIsLargestRoot ψ q ∧
  ∀ β : ℝ, 0 ≤ β → (Phi ψ q < β ↔ q < ψ β)


noncomputable def Zscale (q : ℝ) (W : ℝ → ℝ) (x : ℝ) : ℝ :=
  1 + q * ∫ y in (0 : ℝ)..x, W y


noncomputable def integratedScale (W : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..x, W y


def IsScaleMeasure (W : ℝ → ℝ) (m : Measure ℝ) : Prop :=
  m (Set.Iio (0 : ℝ)) = 0 ∧
  m {0} = ENNReal.ofReal (W 0) ∧
  ∀ a b : ℝ, 0 ≤ a → a ≤ b →
    m (Set.Ioc a b) = ENNReal.ofReal (W b - W a)


noncomputable def tiltedScale (c : ℝ) (W : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (-c * x) * W x


def HasScaleRightDerivative (W : ℝ → ℝ) (x d : ℝ) : Prop :=
  HasDerivWithinAt W d (Set.Ici x) x


noncomputable def scaleRightDerivativeZero (W : ℝ → ℝ) : EReal :=
  Filter.liminf (fun h : ℝ => (((W h - W 0) / h : ℝ) : EReal))
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))


def HasExtendedRightSlope (W : ℝ → ℝ) (d : EReal) : Prop :=
  Filter.Tendsto
    (fun h : ℝ => (((W h - W 0) / h : ℝ) : EReal))
    (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds d)


def RightSlopeAgreesWithAvram (W : ℝ → ℝ) : Prop :=
  scaleRightDerivativeZero W =
    AvramDividend.Classical.derivZeroPlus W


def AtZeroScale (W : ℝ → ℝ) : ℝ := W 0


def IsLawScale
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P ℱ)
    (q : ℝ) (W : ℝ → ℝ) : Prop :=
  IsQScale L.ψ q W


def HasPublishedScaleBridge
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P ℱ)
    (q : ℝ) : Prop :=
  IsScaleTransformDomainBridge L.ψ q ∧
    ∀ W : ℝ → ℝ,
      IsLawScale L q W ↔
        (0 ≤ q ∧ AvramDividend.Classical.IsScaleFunction L q W)


def IsPublishedScaleCandidate
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P ℱ)
    (q : ℝ) (W : ℝ → ℝ) : Prop :=
  0 ≤ q ∧ AvramDividend.Classical.IsScaleFunction L q W


theorem lawScale_iff_published_of_rootDomain
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P ℱ)
    (q : ℝ) (W : ℝ → ℝ)
    (h : IsScaleTransformDomainBridge L.ψ q) :
    IsLawScale L q W ↔ IsPublishedScaleCandidate L q W := by
  constructor
  · intro hs
    rcases hs with ⟨hroot, hneg, hnon, hcont, hmono, hLap⟩
    refine ⟨hroot.1, ?_⟩
    refine ⟨hneg, ?_, hcont, hmono, ?_⟩
    · intro y hy
      exact hnon y
    · intro beta hb hq
      simpa only [neg_mul] using hLap beta hb ((h.2 beta hb).2 hq)
  · intro hp
    rcases hp with ⟨hq, hneg, hnon, hcont, hmono, hLap⟩
    refine ⟨h.1, hneg, ?_, hcont, hmono, ?_⟩
    · intro y
      by_cases hy : 0 ≤ y
      · exact hnon y hy
      · have hlt : y < 0 := lt_of_not_ge hy
        rw [hneg y hlt]
    · intro beta hb hPhi
      simpa only [neg_mul] using hLap beta hb ((h.2 beta hb).1 hPhi)



noncomputable def tauPlus {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (a : ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  sInf {t : WithTop ℝ≥0 | ∃ u : ℝ≥0,
    0 < u ∧ (u : WithTop ℝ≥0) = t ∧ a < X u ω}


noncomputable def tauMinus {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (a : ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  sInf {t : WithTop ℝ≥0 | ∃ u : ℝ≥0,
    0 < u ∧ (u : WithTop ℝ≥0) = t ∧ X u ω < a}


noncomputable def tauWeakAbove {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (a : ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  sInf {t : WithTop ℝ≥0 | ∃ u : ℝ≥0,
    0 < u ∧ (u : WithTop ℝ≥0) = t ∧ a ≤ X u ω}


noncomputable def tauWeakBelow {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (a : ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  sInf {t : WithTop ℝ≥0 | ∃ u : ℝ≥0,
    0 < u ∧ (u : WithTop ℝ≥0) = t ∧ X u ω ≤ a}


noncomputable def hitNegative {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (x : ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  sInf {t : WithTop ℝ≥0 | ∃ u : ℝ≥0,
    0 < u ∧ (u : WithTop ℝ≥0) = t ∧ X u ω = -x}


noncomputable def lastNegativeVisit {Ω : Type*}
    (X : ℝ≥0 → Ω → ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  sSup {t : WithTop ℝ≥0 | ∃ u : ℝ≥0,
    0 < u ∧ (u : WithTop ℝ≥0) = t ∧ X u ω < 0}


noncomputable def discountedAt (q : ℝ) (τ : WithTop ℝ≥0) : ℝ :=
  match τ with
  | ⊤ => 0
  | (t : ℝ≥0) => Real.exp (-q * (t : ℝ))


def IsLeftLimit {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) (v : ℝ) : Prop :=
  0 < t ∧
  Filter.Tendsto (fun s : ℝ≥0 => X s ω)
    (nhdsWithin t (Set.Iio t)) (nhds v)


def IsStoppingTime {Ω : Type*} (m : MeasurableSpace Ω)
    (ℱ : Filtration ℝ≥0 m) (τ : Ω → WithTop ℝ≥0) : Prop :=
  ∀ t : ℝ≥0, @MeasurableSet Ω (ℱ t) {ω | τ ω ≤ (t : WithTop ℝ≥0)}


noncomputable def postPassageValue {Ω : Type*}
    (X : ℝ≥0 → Ω → ℝ) (τ : WithTop ℝ≥0) (ω : Ω) : Option ℝ :=
  match τ with
  | ⊤ => none
  | (t : ℝ≥0) => some (X t ω)


noncomputable def passageOvershoot {Ω : Type*}
    (X : ℝ≥0 → Ω → ℝ) (a : ℝ)
    (τ : WithTop ℝ≥0) (ω : Ω) : Option ℝ :=
  (postPassageValue X τ ω).map (fun v => v - a)


def IsPrePassageValue {Ω : Type*}
    (X : ℝ≥0 → Ω → ℝ)
    (τ : WithTop ℝ≥0) (ω : Ω) (v : ℝ) : Prop :=
  ∃ t : ℝ≥0, (t : WithTop ℝ≥0) = τ ∧
    IsLeftLimit X t ω v


noncomputable def positiveTimeLebesgue : Measure ℝ≥0 :=
  Measure.map Real.toNNReal
    (volume.restrict (Set.Ici (0 : ℝ)))


def IsResolvent {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (q : ℝ) (U : Measure ℝ) : Prop :=
  0 ≤ q ∧
  ∀ A : Set ℝ, MeasurableSet A →
    U A = ∫⁻ t : ℝ≥0,
      ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
        P {ω | X t ω ∈ A} ∂positiveTimeLebesgue


def IsIntervalKilledResolvent {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (q a : ℝ) (U : Measure ℝ) : Prop :=
  0 ≤ q ∧ 0 < a ∧
  ∀ A : Set ℝ, MeasurableSet A →
    U A = ∫⁻ t : ℝ≥0,
      ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
        P {ω | (t : WithTop ℝ≥0) <
          min (tauMinus X 0 ω) (tauPlus X a ω) ∧ X t ω ∈ A} ∂positiveTimeLebesgue


def IsHalflineKilledResolvent {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (q : ℝ) (U : Measure ℝ) : Prop :=
  0 ≤ q ∧
  ∀ A : Set ℝ, MeasurableSet A →
    U A = ∫⁻ t : ℝ≥0,
      ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
        P {ω | (t : WithTop ℝ≥0) < tauMinus X 0 ω ∧ X t ω ∈ A} ∂positiveTimeLebesgue


def IsResolventKernel {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (q : ℝ) (K : ProbabilityTheory.Kernel ℝ ℝ) : Prop :=
  ∀ x : ℝ, IsResolvent P (fun t ω => x + X t ω) q (K x)



def HasLocallyBoundedPaths {Ω : Type*}
    (X : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ (ω : Ω) (t : ℝ≥0),
    BddAbove {y : ℝ | ∃ u : ℝ≥0, u ≤ t ∧ y = X u ω} ∧
    BddBelow {y : ℝ | ∃ u : ℝ≥0, u ≤ t ∧ y = X u ω}


def HasLocallyBoundedPathsAlmostSure {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
    BddAbove {y : ℝ | ∃ u : ℝ≥0, u ≤ t ∧ y = X u ω} ∧
    BddBelow {y : ℝ | ∃ u : ℝ≥0, u ≤ t ∧ y = X u ω}


noncomputable def runningSup {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  sSup {y : ℝ | ∃ u : ℝ≥0, u ≤ t ∧ y = X u ω}


noncomputable def runningInf {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  sInf {y : ℝ | ∃ u : ℝ≥0, u ≤ t ∧ y = X u ω}


noncomputable def reflectAtSup {Ω : Type*}
    (X : ℝ≥0 → Ω → ℝ) (x : ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  max x (runningSup X t ω) - X t ω


noncomputable def reflectAtInf {Ω : Type*}
    (X : ℝ≥0 → Ω → ℝ) (x : ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  X t ω - min (runningInf X t ω) (-x)


noncomputable def reflectedSupExit {Ω : Type*}
    (X : ℝ≥0 → Ω → ℝ) (x a : ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  tauPlus (reflectAtSup X x) a ω


noncomputable def reflectedInfExit {Ω : Type*}
    (X : ℝ≥0 → Ω → ℝ) (x a : ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  tauPlus (reflectAtInf X x) a ω


structure CappedStorage {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (input : ℝ≥0 → Ω → ℝ)
    (initial capacity : ℝ) where
  nonnegativeInitial : 0 ≤ initial
  initialWithinCapacity : initial ≤ capacity
  good : Set Ω
  goodMeasurable : MeasurableSet good
  goodAlmostSure : ∀ᵐ ω ∂P, ω ∈ good
  goodCadlag : ∀ ω ∈ good,
    (∀ t : ℝ≥0, ContinuousWithinAt
      (fun u : ℝ≥0 => input u ω) (Set.Ici t) t) ∧
    (∀ t : ℝ≥0, 0 < t → ∃ left : ℝ,
      Filter.Tendsto (fun u : ℝ≥0 => input u ω)
        (nhdsWithin t (Set.Iio t)) (nhds left))
  workload : ℝ≥0 → Ω → ℝ
  lowerRegulator : ℝ≥0 → Ω → ℝ
  upperRegulator : ℝ≥0 → Ω → ℝ
  workloadMeasurable : ∀ t, Measurable (workload t)
  lowerMeasurable : ∀ t, Measurable (lowerRegulator t)
  upperMeasurable : ∀ t, Measurable (upperRegulator t)
  lowerInitiallyZero : ∀ ω ∈ good, lowerRegulator 0 ω = 0
  upperInitiallyZero : ∀ ω ∈ good, upperRegulator 0 ω = 0
  balance : ∀ t ω, ω ∈ good →
    workload t ω = initial + input t ω +
      lowerRegulator t ω - upperRegulator t ω
  range : ∀ t ω, ω ∈ good →
    0 ≤ workload t ω ∧ workload t ω ≤ capacity
  lowerMonotone : ∀ ω ∈ good, ∀ s t, s ≤ t →
    lowerRegulator s ω ≤ lowerRegulator t ω
  upperMonotone : ∀ ω ∈ good, ∀ s t, s ≤ t →
    upperRegulator s ω ≤ upperRegulator t ω
  lowerContact : ∀ ω ∈ good, ∀ s t, s ≤ t →
    (∀ u, s ≤ u → u ≤ t → 0 < workload u ω) →
    lowerRegulator s ω = lowerRegulator t ω
  upperContact : ∀ ω ∈ good, ∀ s t, s ≤ t →
    (∀ u, s ≤ u → u ≤ t → workload u ω < capacity) →
    upperRegulator s ω = upperRegulator t ω


def HasUniqueCappedStorage {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (initial capacity : ℝ) : Prop :=
  ∃ S : CappedStorage P X initial capacity,
    ∀ T : CappedStorage P X initial capacity,
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        S.workload t ω = T.workload t ω ∧
        S.lowerRegulator t ω = T.lowerRegulator t ω ∧
        S.upperRegulator t ω = T.upperRegulator t ω


noncomputable def cappedEmptyingTime {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℝ≥0 → Ω → ℝ} {x c : ℝ}
    (S : CappedStorage P X x c) (ω : Ω) : WithTop ℝ≥0 :=
  tauWeakBelow S.workload 0 ω


noncomputable def supremumReflectedScaleResolvent
    (W : ℝ → ℝ → ℝ) (q x a : ℝ) : Measure ℝ :=
  let V := W q
  let da := derivWithin V (Set.Ici a) a
  (ENNReal.ofReal (V (a - x) * V 0 / da)) •
    (Measure.dirac (0 : ℝ)) +
  (volume.restrict (Set.Ioo 0 a)).withDensity
    (fun y : ℝ =>
      ENNReal.ofReal
        (V (a - x) * derivWithin V (Set.Ici y) y / da -
          V (y - x)))


def IsSupremumReflectedPotential {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (q x a : ℝ) (U : Measure ℝ) : Prop :=
  0 ≤ q ∧ 0 ≤ x ∧ x ≤ a ∧ 0 < a ∧
  ∀ A : Set ℝ, MeasurableSet A →
    U A = ∫⁻ t : ℝ≥0,
      ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
        P {ω | (t : WithTop ℝ≥0) <
          reflectedSupExit X x a ω ∧
          reflectAtSup X x t ω ∈ A} ∂positiveTimeLebesgue


def IsInfimumReflectedPotential {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (q x a : ℝ) (U : Measure ℝ) : Prop :=
  0 ≤ q ∧ 0 ≤ x ∧ x ≤ a ∧ 0 < a ∧
  ∀ A : Set ℝ, MeasurableSet A →
    U A = ∫⁻ t : ℝ≥0,
      ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
        P {ω | (t : WithTop ℝ≥0) <
          reflectedInfExit X x a ω ∧
          reflectAtInf X x t ω ∈ A} ∂positiveTimeLebesgue



noncomputable def gouItoApprox {Ω : Type*}
    (X : ℝ≥0 → Ω → ℝ) (reversion : ℝ)
    (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    Real.exp (reversion * (t : ℝ) * ((k : ℝ) / (n + 1))) *
      (X (t * ((↑(k + 1) : ℝ≥0) / (↑(n + 1) : ℝ≥0))) ω -
       X (t * ((↑k : ℝ≥0) / (↑(n + 1) : ℝ≥0))) ω)


def IsGouItoIntegral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (reversion : ℝ) (I : ℝ≥0 → Ω → ℝ) : Prop :=
  0 < reversion ∧
  ∀ (t : ℝ≥0) (eps : ℝ), 0 < eps →
    Filter.Tendsto
      (fun n : ℕ =>
        P {ω | eps ≤ |gouItoApprox X reversion n t ω - I t ω|})
      Filter.atTop (nhds (0 : ENNReal))


def HasAlmostSureCadlagIntegral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (I : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
    ContinuousWithinAt (fun s : ℝ≥0 => I s ω) (Set.Ici t) t ∧
    (0 < t → ∃ left : ℝ,
      Filter.Tendsto (fun s : ℝ≥0 => I s ω)
        (nhdsWithin t (Set.Iio t)) (nhds left))


def HasGOUAdaptedIntegral {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (ℱ : Filtration ℝ≥0 mΩ) (I : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ t : ℝ≥0, @Measurable Ω ℝ (ℱ t) inferInstance (I t)


def IsGOURightContinuousFiltration {Ω : Type*}
    [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 mΩ) : Prop :=
  ∀ (t : ℝ≥0) (A : Set Ω),
    @MeasurableSet Ω (ℱ t) A ↔
      ∀ s : ℝ≥0, t < s → @MeasurableSet Ω (ℱ s) A


structure GOUInput (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] where
  driver : SpectrallyNegativeModel Ω P
  meanReversion : ℝ
  positiveMeanReversion : 0 < meanReversion
  filtration : Filtration ℝ≥0 mΩ
  filtrationIsCompletedNatural :
    HasCompletedNaturalFiltration P driver filtration
  filtrationRightContinuous :
    IsGOURightContinuousFiltration filtration
  stochasticIntegral : ℝ≥0 → Ω → ℝ
  integralIsIto :
    IsGouItoIntegral P driver.X meanReversion stochasticIntegral
  integralAdapted :
    HasGOUAdaptedIntegral filtration stochasticIntegral
  integralCadlag :
    HasAlmostSureCadlagIntegral P stochasticIntegral


noncomputable def GOUPath {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (M : GOUInput Ω P)
    (y : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (-M.meanReversion * (t : ℝ)) *
    (y + M.stochasticIntegral t ω)


noncomputable def GOUExit {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (M : GOUInput Ω P)
    (y a : ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  tauPlus (GOUPath M y) a ω


def HasGOUConstruction {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (reversion : ℝ) : Prop :=
  0 < reversion ∧
  ∃ M : GOUInput Ω P, M.driver = D ∧ M.meanReversion = reversion


def GOUIndistinguishable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (I J : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂P, ∀ t : ℝ≥0, I t ω = J t ω


def GOUVersionUniquenessObligation {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) : Prop :=
  ∀ I J : ℝ≥0 → Ω → ℝ,
    HasAlmostSureCadlagIntegral P I →
    HasAlmostSureCadlagIntegral P J →
    (∀ t : ℝ≥0, ∀ᵐ ω ∂P, I t ω = J t ω) →
    GOUIndistinguishable P I J


def GOUExitVersionLawObligation {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] : Prop :=
  ∀ (M N : GOUInput Ω P) (y a : ℝ),
    M.driver = N.driver →
    M.meanReversion = N.meanReversion →
    GOUIndistinguishable P M.stochasticIntegral N.stochasticIntegral →
    ∀ᵐ ω ∂P, GOUExit M y a ω = GOUExit N y a ω


noncomputable def Htransform (ψ : ℝ → ℝ)
    (reversion ν x : ℝ) : ℝ :=
  ∫ u in Set.Ioi (0 : ℝ),
    Real.exp (x * u -
      (1 / reversion) * (∫ v in (0 : ℝ)..u, ψ v / v)) *
      u ^ (ν - 1 : ℝ) ∂volume


def HIsIntegrable (ψ : ℝ → ℝ) (reversion ν x : ℝ) : Prop :=
  0 < reversion ∧ 0 < ν ∧
  IntegrableOn
    (fun u : ℝ => Real.exp (x * u -
        (1 / reversion) * (∫ v in (0 : ℝ)..u, ψ v / v)) * u ^ (ν - 1))
    (Set.Ioi (0 : ℝ)) volume


def IsGOUPositiveHDomain (ψ : ℝ → ℝ)
    (reversion θ y a : ℝ) : Prop :=
  0 < reversion ∧ 0 < θ ∧
  HIsIntegrable ψ reversion (θ / reversion) y ∧
  HIsIntegrable ψ reversion (θ / reversion) a ∧
  Htransform ψ reversion (θ / reversion) a ≠ 0


noncomputable def GOUPositiveHRatio (ψ : ℝ → ℝ)
    (reversion θ y a : ℝ) : ℝ :=
  Htransform ψ reversion (θ / reversion) y /
    Htransform ψ reversion (θ / reversion) a


def IsGOUZeroHBoundary (ψ : ℝ → ℝ)
    (reversion y a p : ℝ) : Prop :=
  (∀ᶠ θ : ℝ in nhdsWithin 0 (Set.Ioi 0),
    IsGOUPositiveHDomain ψ reversion θ y a) ∧
  Filter.Tendsto
    (fun θ : ℝ => GOUPositiveHRatio ψ reversion θ y a)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds p)


def IsGOUTheorem812TransformConclusion {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (M : GOUInput Ω P) (ψ : ℝ → ℝ) (y a : ℝ) : Prop :=
  (∀ θ : ℝ, 0 < θ →
    IsGOUPositiveHDomain ψ M.meanReversion θ y a ∧
    (∫ ω, discountedAt θ (GOUExit M y a ω) ∂P) =
      GOUPositiveHRatio ψ M.meanReversion θ y a) ∧
  IsGOUZeroHBoundary ψ M.meanReversion y a
    (∫ ω, discountedAt 0 (GOUExit M y a ω) ∂P)


noncomputable def stableLaplace (c α β : ℝ) : ℝ :=
  c * β ^ α


noncomputable def mittagLeffler (α z : ℝ) : ℝ :=
  ∑' n : ℕ, z ^ n / Real.Gamma (1 + α * n)


def MittagLefflerSummable (α z : ℝ) : Prop :=
  0 < α ∧ Summable (fun n : ℕ =>
    z ^ n / Real.Gamma (1 + α * n))


def HasNonnegativeHeightSupport (n : Measure ℝ) : Prop :=
  n (Set.Iio (0 : ℝ)) = 0


noncomputable def claimLossRate (componentJumpMeasure : Measure ℝ) : ℝ :=
  ∫ x in Set.Iio (0 : ℝ), -x ∂componentJumpMeasure


structure CompetingClaimData (n : ℕ) where
  drift : Fin n → ℝ
  jumpLaw : Fin n → Measure ℝ


def GOUHasLogJumpIntegrability (jumpMeasure : Measure ℝ) : Prop :=
  (∫⁻ x in Set.Iio (-1 : ℝ),
    ENNReal.ofReal (Real.log |x|) ∂jumpMeasure) < ⊤


def IsStableExponent (ψ : ℝ → ℝ) (c α : ℝ) : Prop :=
  0 < c ∧ 1 < α ∧ α ≤ 2 ∧
  ∀ β : ℝ, 0 ≤ β → ψ β = stableLaplace c α β


def IsStableSubordinatorExponent (phi : ℝ → ℝ)
    (c α : ℝ) : Prop :=
  0 < c ∧ 0 < α ∧ α < 1 ∧
  ∀ β : ℝ, 0 ≤ β → phi β = stableLaplace c α β


structure ExcursionSystem (E : Type*) [MeasurableSpace E] where
  excursionLaw : Measure E
  height : E → ℝ
  heightMeasurable : Measurable height

noncomputable def excursionHeightMeasure {E : Type*}
    [MeasurableSpace E] (S : ExcursionSystem E) : Measure ℝ :=
  Measure.map S.height S.excursionLaw


structure CompetingRiskPathData (Ω : Type*) (n : ℕ) where
  total : ℝ≥0 → Ω → ℝ
  component : Fin n → ℝ≥0 → Ω → ℝ
  pathSum : ∀ (t : ℝ≥0) (ω : Ω),
    total t ω = ∑ i : Fin n, component i t ω

end Kyprianou.Ch08

namespace Kyprianou.Ch08.StageB





def shifted {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (x : ℝ) : ℝ≥0 → Ω → ℝ :=
  fun t ω => x + X t ω


noncomputable def killedIntervalDensity
    (W : ℝ → ℝ) (a x y : ℝ) : ℝ :=
  W x * W (a - y) / W a - W (x - y)


noncomputable def killedHalflineDensity
    (ψ : ℝ → ℝ) (q : ℝ) (W : ℝ → ℝ) (x y : ℝ) : ℝ :=
  Real.exp (-(Phi ψ q) * y) * W x - W (x - y)


noncomputable def unrestrictedPotentialDensity
    (ψ : ℝ → ℝ) (q : ℝ) (W : ℝ → ℝ) (z : ℝ) : ℝ :=
  deriv (Phi ψ) q * Real.exp (-(Phi ψ q) * z) - W (-z)


def HasSourceScaleFamily (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ) : Prop :=
  ∀ q : ℝ, 0 ≤ q → IsQScale ψ q (W q)


def result8_6 : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ q : ℝ, 0 ≤ q →
      ((W q 0 = 0) ↔
        ¬ HasBoundedVariationTriplet
            D.gaussianCoefficient D.triplet.levyMeasure) ∧
      (HasBoundedVariationTriplet
        D.gaussianCoefficient D.triplet.levyMeasure →
        0 < bvDrift D.triplet.drift D.triplet.levyMeasure ∧
        W q 0 = (bvDrift D.triplet.drift D.triplet.levyMeasure)⁻¹)


def result8_7 : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ (q a x : ℝ), 0 ≤ q → 0 < a → 0 ≤ x → x ≤ a →
      ∃ U : Measure ℝ,
        IsIntervalKilledResolvent P (shifted D.X x) q a U ∧
        U = (volume.restrict (Set.Icc 0 a)).withDensity
          (fun y : ℝ =>
            ENNReal.ofReal (killedIntervalDensity (W q) a x y))


def result8_8 : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ (q x : ℝ), 0 ≤ q → 0 ≤ x →
      ∃ U : Measure ℝ,
        IsHalflineKilledResolvent P (shifted D.X x) q U ∧
        U = (volume.restrict (Set.Ici 0)).withDensity
          (fun y : ℝ =>
            ENNReal.ofReal (killedHalflineDensity ψ q (W q) x y))


def result8_9 : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ (q x : ℝ), 0 < q →
      DifferentiableAt ℝ (Phi ψ) q ∧
      ∃ U : Measure ℝ,
        IsResolvent P (shifted D.X x) q U ∧
        U = volume.withDensity
          (fun y : ℝ =>
            ENNReal.ofReal
              (unrestrictedPotentialDensity ψ q (W q) (x-y)))


def result8_12 : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (reversion a y : ℝ),
    0 < reversion → 0 < a → y ≤ a →
    GOUHasLogJumpIntegrability D.triplet.levyMeasure →
    (¬ HasBoundedVariationTriplet D.gaussianCoefficient D.triplet.levyMeasure ∨
      (HasBoundedVariationTriplet D.gaussianCoefficient
         D.triplet.levyMeasure ∧
       reversion * a < bvDrift D.triplet.drift D.triplet.levyMeasure)) →
    HasGOUConstruction P D reversion ∧
    ∀ M : GOUInput Ω P,
      M.driver = D → M.meanReversion = reversion →
      IsGOUTheorem812TransformConclusion M
        (tripletLaplace D.triplet.drift
          D.gaussianCoefficient D.triplet.levyMeasure) y a







noncomputable def downExpectation {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) (q x : ℝ) : ℝ :=
  ∫ ω, discountedAt q (tauMinus (shifted X x) 0 ω) ∂P


noncomputable def upBeforeDownExpectation {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) (q x a : ℝ) : ℝ :=
  ∫ ω,
    (if tauPlus (shifted X x) a ω <
          tauMinus (shifted X x) 0 ω
     then discountedAt q (tauPlus (shifted X x) a ω)
     else 0) ∂P


noncomputable def downBeforeUpExpectation {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) (q x a : ℝ) : ℝ :=
  ∫ ω,
    (if tauMinus (shifted X x) 0 ω <
          tauPlus (shifted X x) a ω
     then discountedAt q (tauMinus (shifted X x) 0 ω)
     else 0) ∂P


def HasPositiveFiniteRightPsiSlope (ψ : ℝ → ℝ) (d : ℝ) : Prop :=
  0 < d ∧
  Filter.Tendsto (fun h : ℝ => (ψ h - ψ 0) / h)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds d)


def result8_1 : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P),
    ∃ (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ ∧
      HasSourceScaleFamily ψ W ∧
      (∀ (q x : ℝ), 0 < q →
        downExpectation P D.X q x =
          Zscale q (W q) x -
            q / Phi ψ q * W q x) ∧
      (∀ (x : ℝ) (d : ℝ),
        HasPositiveFiniteRightPsiSlope ψ d →
        downExpectation P D.X 0 x = 1 - d * W 0 x) ∧
      ((¬ ∃ d : ℝ, HasPositiveFiniteRightPsiSlope ψ d) →
        ∀ x : ℝ, downExpectation P D.X 0 x = 1) ∧
      (∀ (q x a : ℝ), 0 ≤ q → 0 < a → x ≤ a →
        0 < W q a ∧
        upBeforeDownExpectation P D.X q x a =
          W q x / W q a ∧
        downBeforeUpExpectation P D.X q x a =
          Zscale q (W q) x -
            Zscale q (W q) a * W q x / W q a)


def result8_3 : Prop :=
  ∀ (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ),
    HasSourceScaleFamily ψ W →
    ∀ x : ℝ, 0 ≤ x →
      ∃ F : ℂ → ℂ,
        Differentiable ℂ F ∧
        ∀ q : ℝ, 0 ≤ q → F (q : ℂ) = (W q x : ℂ)


def result8_5 : Prop :=
  ∀ (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ),
    HasSourceScaleFamily ψ W →
    ∀ x : ℝ, 0 < x →
      ∃ F : ℂ → ℂ,
        Differentiable ℂ F ∧
        ∀ q : ℝ, 0 ≤ q → F (q : ℂ) = (Zscale q (W q) x : ℂ)


noncomputable def reflectedSupJointPayoff {Ω : Type*}
    (X : ℝ≥0 → Ω → ℝ) (q θ x a : ℝ) (ω : Ω) : ℝ :=
  match reflectedSupExit X x a ω with
  | ⊤ => 0
  | (t : ℝ≥0) =>
      Real.exp (-q * (t : ℝ) - θ * reflectAtSup X x t ω)


def result8_10_i : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsFullMomentLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ (q θ x a : ℝ), 0 ≤ q → 0 < a → 0 ≤ x → x ≤ a →
      Integrable (fun ω => Real.exp (θ * D.X 1 ω)) P →
      let p := q - ψ θ
      let V := tiltedScale θ (W q)
      let Zv := Zscale p V
      let derivative := derivWithin V (Set.Ici a) a
      HasDerivWithinAt V derivative (Set.Ici a) a ∧
      ((derivative + θ * V a ≠ 0 →
        (∫ ω, reflectedSupJointPayoff D.X q θ x a ω ∂P) =
          Real.exp (-θ * x) *
            (Zv (a - x) -
             V (a - x) *
               (p * V a + θ * Zv a) /
               (derivative + θ * V a))) ∧
       (derivative + θ * V a = 0 →
        (∫ ω, reflectedSupJointPayoff D.X q θ x a ω ∂P) = 0))


def result8_10_ii : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ (q x a : ℝ), 0 ≤ q → 0 < a → 0 ≤ x → x ≤ a →
      Zscale q (W q) a ≠ 0 ∧
      (∫ ω, discountedAt q (reflectedInfExit D.X x a ω) ∂P) =
        Zscale q (W q) x / Zscale q (W q) a


def result8_10 : Prop := result8_10_i ∧ result8_10_ii


def result8_11_i : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ (q x a : ℝ), 0 ≤ q → 0 < a → 0 ≤ x → x < a →
      let V := W q
      let da := derivWithin V (Set.Ici a) a
      HasDerivWithinAt V da (Set.Ici a) a ∧
      ∃ U : Measure ℝ,
        IsSupremumReflectedPotential P D.X q x a U ∧
        (da ≠ 0 →
          U = supremumReflectedScaleResolvent W q x a) ∧
        (da = 0 →
          q = 0 ∧ U {0} = ⊤ ∧
          (∀ n : ℕ,
            0 < derivWithin
              (W (1 / (((n + 1 : ℕ) : ℝ))))
              (Set.Ici a) a) ∧
          ∀ A : Set ℝ, MeasurableSet A →
            U A =
              ⨆ n : ℕ,
                (supremumReflectedScaleResolvent W
                  (1 / (((n + 1 : ℕ) : ℝ))) x a) A)


def result8_11_ii : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ (q x a : ℝ), 0 ≤ q → 0 < a → 0 ≤ x → x < a →
      Zscale q (W q) a ≠ 0 ∧
      ∃ U : Measure ℝ,
        IsInfimumReflectedPotential P D.X q x a U ∧
        U = (volume.restrict (Set.Ico 0 a)).withDensity
          (fun y : ℝ =>
            ENNReal.ofReal
              (W q (a - y) * Zscale q (W q) x /
                Zscale q (W q) a - W q (x - y)))


def result8_11 : Prop := result8_11_i ∧ result8_11_ii







def exercise8_2_i : Prop :=
  ∀ (α q β : ℝ) (W : ℝ → ℝ → ℝ),
    1 < α → α < 2 → 0 < q → q ^ (1 / α) < β →
    HasSourceScaleFamily (fun v : ℝ => v ^ α) W →
    Summable (fun n : ℕ =>
      q ^ n * β ^ (-(α * (n + 1) + 1))) ∧
    (∫ x in Set.Ioi (0 : ℝ),
      Real.exp (-β * x) * integratedScale (W q) x ∂volume) =
      (β * (β ^ α - q))⁻¹ ∧
    (β * (β ^ α - q))⁻¹ =
      ∑' n : ℕ, q ^ n * β ^ (-(α * (n + 1) + 1))


def exercise8_2_ii : Prop :=
  ∀ (α q x : ℝ) (W : ℝ → ℝ → ℝ),
    1 < α → α < 2 → 0 ≤ q → 0 ≤ x →
    HasSourceScaleFamily (fun v : ℝ => v ^ α) W →
    Zscale q (W q) x =
      ∑' n : ℕ, q ^ n * x ^ (α * n) / Real.Gamma (1 + α * n) ∧
    Zscale q (W q) x = mittagLeffler α (q * x ^ α)


def exercise8_2_iii : Prop :=
  ∀ (α q x : ℝ) (W : ℝ → ℝ → ℝ),
    1 < α → α < 2 → 0 ≤ q → 0 ≤ x →
    HasSourceScaleFamily (fun v : ℝ => v ^ α) W →
    W q x = α * x ^ (α-1) *
      deriv (mittagLeffler α) (q * x ^ α)


def exercise8_2_iv : Prop :=
  ∀ (q x : ℝ) (W : ℝ → ℝ → ℝ),
    0 ≤ q → 0 ≤ x →
    HasSourceScaleFamily (fun β : ℝ => β ^ 2 / 2) W →
    W q x =
      (if q = 0 then 2 * x
       else Real.sqrt (2 / q) *
         Real.sinh (Real.sqrt (2 * q) * x)) ∧
    Zscale q (W q) x =
      Real.cosh (Real.sqrt (2 * q) * x)


def exercise8_2 : Prop :=
  exercise8_2_i ∧ exercise8_2_ii ∧
  exercise8_2_iii ∧ exercise8_2_iv


def exercise8_5_i : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    (∀ q : ℝ, 0 < q →
      Filter.Tendsto
        (fun z : ℝ => Zscale q (W q) z / W q z)
        Filter.atTop (nhds (q / Phi ψ q))) ∧
    (∃ c : ℝ,
      Filter.Tendsto
        (fun q : ℝ => q / Phi ψ q)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds c) ∧
      Filter.Tendsto
        (fun z : ℝ => Zscale 0 (W 0) z / W 0 z)
        Filter.atTop (nhds c)) ∧
    (∀ q x : ℝ, 0 ≤ q →
      Filter.Tendsto
        (fun a : ℝ => W q (a - x) / W q a)
        Filter.atTop (nhds (Real.exp (-Phi ψ q * x))))


def exercise8_5_ii : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ q : ℝ, 0 ≤ q →
      (¬ HasBoundedVariationTriplet
        D.gaussianCoefficient D.triplet.levyMeasure →
        (0 < D.gaussianCoefficient ^ 2 →
          HasExtendedRightSlope (W q)
            (((2 / D.gaussianCoefficient ^ 2 : ℝ) : EReal))) ∧
        (D.gaussianCoefficient = 0 →
          HasExtendedRightSlope (W q) (⊤ : EReal))) ∧
      (HasBoundedVariationTriplet
        D.gaussianCoefficient D.triplet.levyMeasure →
        (D.triplet.levyMeasure (Set.Iio (0 : ℝ)) < ⊤ →
          HasExtendedRightSlope (W q)
            ((((D.triplet.levyMeasure (Set.Iio (0 : ℝ))).toReal + q) /
              (bvDrift D.triplet.drift D.triplet.levyMeasure) ^ 2 : ℝ))) ∧
        (D.triplet.levyMeasure (Set.Iio (0 : ℝ)) = ⊤ →
          HasExtendedRightSlope (W q) (⊤ : EReal)))


def exercise8_5 : Prop :=
  exercise8_5_i ∧ exercise8_5_ii


noncomputable def stableOvershootCDF
    (α y : ℝ) : ℝ :=
  Real.sin (Real.pi * (α - 1)) / Real.pi *
    ∫ t in (0 : ℝ)..y, t ^ (-(α - 1)) / (1 + t)


def StableOvershootEvent {Ω : Type*}
    (X : ℝ≥0 → Ω → ℝ) (x y : ℝ) (ω : Ω) : Prop :=
  tauMinus (shifted X x) 0 ω <
    tauPlus (shifted X x) 1 ω ∧
  ∃ v : ℝ,
    postPassageValue (shifted X x)
      (tauMinus (shifted X x) 0 ω) ω = some v ∧
    -v ≤ y


def exercise8_12_i : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (α x y : ℝ),
    1 < α → α < 2 → 0 < x → x < 1 → 0 ≤ y →
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D)
      (fun β : ℝ => β ^ α) →
    (P {ω | StableOvershootEvent D.X x y ω}).toReal =
      stableOvershootCDF α (y / x) -
      x ^ (α - 1) * stableOvershootCDF α y


def exercise8_12_ii : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (α x y : ℝ),
    1 < α → α < 2 → 0 < x → x < 1 → 0 ≤ y →
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D)
      (fun β : ℝ => β ^ α) →
    (P {ω | StableOvershootEvent D.X x y ω}).toReal =
      Real.sin (Real.pi * (α - 1)) / Real.pi *
      x ^ (α - 1) * (1 - x) *
        ∫ t in (0 : ℝ)..y,
          t ^ (-(α - 1)) / ((t + 1) * (t + x))


def exercise8_12 : Prop :=
  exercise8_12_i ∧ exercise8_12_ii







def HasNegativeRightPsiSlope (ψ : ℝ → ℝ) : Prop :=
  ∃ d : EReal, d < 0 ∧
    Filter.Tendsto
      (fun h : ℝ => (((ψ h - ψ 0) / h : ℝ) : EReal))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds d)


def exercise8_1 : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (F : Filtration ℝ≥0 mΩ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasCompletedNaturalFiltration P D F →
    HasNegativeRightPsiSlope ψ →
    ∀ (t : ℝ≥0) (A : Set Ω),
      @MeasurableSet Ω (F t) A →
      Filter.Tendsto
        (fun a : ℝ =>
          (P (A ∩ {ω | tauPlus D.X a ω ≠ ⊤})).toReal /
            (P {ω | tauPlus D.X a ω ≠ ⊤}).toReal)
        Filter.atTop
        (nhds ((esscherFiniteTimeLaw
          (SpectrallyNegativeModel.toData P D) ψ
          (Phi ψ 0) t) A).toReal)


def exercise8_6 : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ x : ℝ, x ≤ 0 →
      (D.gaussianCoefficient = 0 →
        (P {ω | postPassageValue D.X
          (tauMinus D.X x ω) ω = some x}).toReal = 0) ∧
      (0 < D.gaussianCoefficient ^ 2 →
        HasDerivWithinAt (W 0)
          (derivWithin (W 0) (Set.Ici (-x)) (-x))
          (Set.Ici (-x)) (-x) ∧
        (P {ω | postPassageValue D.X
          (tauMinus D.X x ω) ω = some x}).toReal =
          D.gaussianCoefficient ^ 2 / 2 *
            (derivWithin (W 0) (Set.Ici (-x)) (-x) -
              Phi ψ 0 * W 0 (-x)))


noncomputable def lastExitShifted
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (y : ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  lastNegativeVisit (shifted X y) ω


def NeverNegative {Ω : Type*}
    (X : ℝ≥0 → Ω → ℝ) (x : ℝ) (ω : Ω) : Prop :=
  ∀ t : ℝ≥0, 0 < t → 0 ≤ x + X t ω


def exercise8_10_i : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    (∀ᵐ ω ∂P, Filter.Tendsto (fun t : ℝ≥0 => D.X t ω)
      Filter.atTop Filter.atTop) →
    ∀ (q y : ℝ), 0 < q →
      (∫ ω, discountedAt q (lastExitShifted D.X y ω) ∂P) =
        q * ∫ x in Set.Ici (0 : ℝ),
          unrestrictedPotentialDensity ψ q (W q) (x - y) *
            (P {ω | NeverNegative D.X x ω}).toReal ∂volume


def exercise8_10_ii : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    (∀ᵐ ω ∂P, Filter.Tendsto (fun t : ℝ≥0 => D.X t ω)
      Filter.atTop Filter.atTop) →
    ∃ d : ℝ,
      HasPositiveFiniteRightPsiSlope ψ d ∧
      (∀ (q y : ℝ), 0 < q → y ≤ 0 →
        (∫ ω, discountedAt q (lastExitShifted D.X y ω) ∂P) =
          d * deriv (Phi ψ) q * Real.exp (Phi ψ q * y)) ∧
      (HasBoundedVariationTriplet
        D.gaussianCoefficient D.triplet.levyMeasure →
        (P {ω | lastExitShifted D.X 0 ω = 0}).toReal =
          d / bvDrift D.triplet.drift D.triplet.levyMeasure) ∧
      (¬ HasBoundedVariationTriplet
        D.gaussianCoefficient D.triplet.levyMeasure →
        (P {ω | lastExitShifted D.X 0 ω = 0}).toReal = 0)


noncomputable def discountedPositiveLastExit
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (q y : ℝ) (ω : Ω) : ℝ :=
  if (0 : WithTop ℝ≥0) < lastExitShifted X y ω
  then discountedAt q (lastExitShifted X y ω)
  else 0


noncomputable def downOvershootTilt
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (q θ y : ℝ) (ω : Ω) : ℝ :=
  match tauMinus (shifted X y) 0 ω with
  | ⊤ => 0
  | (t : ℝ≥0) =>
      Real.exp (-q * (t : ℝ) + θ * (y + X t ω))


def exercise8_10_iii : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    (∀ᵐ ω ∂P, Filter.Tendsto (fun t : ℝ≥0 => D.X t ω)
      Filter.atTop Filter.atTop) →
    ∃ d : ℝ,
      HasPositiveFiniteRightPsiSlope ψ d ∧
      ∀ (q y : ℝ), 0 < q → 0 < y →
        (∫ ω, discountedPositiveLastExit D.X q y ω ∂P) =
          d * deriv (Phi ψ) q *
            ∫ ω, downOvershootTilt D.X q (Phi ψ q) y ω ∂P


def exercise8_10_iv : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    (∀ᵐ ω ∂P, Filter.Tendsto (fun t : ℝ≥0 => D.X t ω)
      Filter.atTop Filter.atTop) →
    ∃ d : ℝ,
      HasPositiveFiniteRightPsiSlope ψ d ∧
      ∀ (q y : ℝ), 0 < q → 0 < y →
        (∫ ω, discountedPositiveLastExit D.X q y ω ∂P) =
          d * deriv (Phi ψ) q *
            Real.exp (Phi ψ q * y) - d * W q y

def exercise8_10 : Prop :=
  exercise8_10_i ∧ exercise8_10_ii ∧
  exercise8_10_iii ∧ exercise8_10_iv


def exercise8_11_i : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (q x a : ℝ),
    0 ≤ q → 0 < a → 0 < x → x ≤ a →
    (∫ ω, discountedAt q (reflectedInfExit D.X x a ω) ∂P) =
      downBeforeUpExpectation P D.X q x a *
        (∫ ω, discountedAt q (reflectedInfExit D.X 0 a ω) ∂P) +
      upBeforeDownExpectation P D.X q x a


def exercise8_11_ii : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    HasBoundedVariationTriplet D.gaussianCoefficient
      D.triplet.levyMeasure →
    ∀ (q x a : ℝ), 0 ≤ q → 0 < a → 0 ≤ x → x ≤ a →
      Zscale q (W q) a ≠ 0 ∧
      (∫ ω, discountedAt q (reflectedInfExit D.X x a ω) ∂P) =
        Zscale q (W q) x / Zscale q (W q) a


def exercise8_11_iii : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ (q x c : ℝ), 0 < q → 0 < x → x < c →
      HasUniqueCappedStorage P D.X x c ∧
      Zscale q (W q) c ≠ 0 ∧
      ∀ S : CappedStorage P D.X x c,
        (∫ ω, discountedAt q (cappedEmptyingTime S ω) ∂P) =
          Zscale q (W q) (c - x) / Zscale q (W q) c

def exercise8_11 : Prop :=
  exercise8_11_i ∧ exercise8_11_ii ∧ exercise8_11_iii







noncomputable def descendingJumpTail
    (jumpMeasure : Measure ℝ) (y : ℝ) : ℝ :=
  (jumpMeasure (Set.Iio (-y))).toReal


def DriftsToPositiveInfinity {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂P,
    Filter.Tendsto (fun t : ℝ≥0 => X t ω)
      Filter.atTop Filter.atTop


def DriftsToNegativeInfinity {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂P,
    Filter.Tendsto (fun t : ℝ≥0 => X t ω)
      Filter.atTop Filter.atBot


noncomputable def measureConvolve
    (μ ν : Measure ℝ) : Measure ℝ :=
  Measure.map (fun p : ℝ × ℝ => p.1 + p.2) (μ.prod ν)


noncomputable def measureConvolvePow
    (ν : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac (0 : ℝ)
  | n + 1 => measureConvolve ν (measureConvolvePow ν n)


noncomputable def descendingRenewalMeasure
    (jumpMeasure : Measure ℝ) (d : ℝ) : Measure ℝ :=
  (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
    (fun y : ℝ =>
      ENNReal.ofReal ((d)⁻¹ * descendingJumpTail jumpMeasure y))


def exercise8_3_i : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P),
    HasBoundedVariationTriplet
      D.gaussianCoefficient D.triplet.levyMeasure →
    DriftsToPositiveInfinity P D.X →
    let d := bvDrift D.triplet.drift D.triplet.levyMeasure
    0 < d ∧ (d)⁻¹ *
      (∫ y in Set.Ioi (0 : ℝ),
        descendingJumpTail D.triplet.levyMeasure y ∂volume) < 1


def exercise8_3_ii : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasBoundedVariationTriplet
      D.gaussianCoefficient D.triplet.levyMeasure →
    DriftsToPositiveInfinity P D.X →
    HasSourceScaleFamily ψ W →
    let d := bvDrift D.triplet.drift D.triplet.levyMeasure
    let ν := descendingRenewalMeasure D.triplet.levyMeasure d
    ∃ m : Measure ℝ,
      IsScaleMeasure (W 0) m ∧
      (∀ β : ℝ, 0 < β →
        (∫ x in Set.Ici (0 : ℝ),
          Real.exp (-β * x) ∂m) =
          (d - ∫ y in Set.Ioi (0 : ℝ),
            Real.exp (-β * y) *
              descendingJumpTail D.triplet.levyMeasure y ∂volume)⁻¹) ∧
      (∀ A : Set ℝ, MeasurableSet A →
        m A =
          (ENNReal.ofReal ((d)⁻¹)) *
          ∑' n : ℕ, (measureConvolvePow ν n) A)


def exercise8_3_iii : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    HasBoundedVariationTriplet
      D.gaussianCoefficient D.triplet.levyMeasure →
    DriftsToPositiveInfinity P D.X →
    ∀ (rate μ : ℝ), 0 < rate → 0 < μ →
      (∀ y : ℝ, 0 < y →
        descendingJumpTail D.triplet.levyMeasure y =
          rate * Real.exp (-μ * y)) →
      let d := bvDrift D.triplet.drift D.triplet.levyMeasure
      0 < d * μ - rate ∧
      ∀ x : ℝ, 0 ≤ x →
        W 0 x = (d)⁻¹ *
          (1 + rate / (d * μ - rate) *
            (1 - Real.exp (-(μ - rate / d) * x)))

def exercise8_3 : Prop :=
  exercise8_3_i ∧ exercise8_3_ii ∧ exercise8_3_iii


def HasAtomlessNegativeLevyMeasure (jumpMeasure : Measure ℝ) : Prop :=
  ∀ x : ℝ, x < 0 → jumpMeasure {x} = 0


def HasSmoothJumpTail
    (jumpMeasure : Measure ℝ) (n : ℕ) : Prop :=
  ContDiffOn ℝ n
    (descendingJumpTail jumpMeasure) (Set.Ioi (0 : ℝ))


def exercise8_4_i : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    HasBoundedVariationTriplet D.gaussianCoefficient
      D.triplet.levyMeasure →
    DriftsToPositiveInfinity P D.X →
    (ContDiffOn ℝ 1 (W 0) (Set.Ioi (0 : ℝ)) ↔
      HasAtomlessNegativeLevyMeasure D.triplet.levyMeasure)


def exercise8_4_ii : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    HasBoundedVariationTriplet D.gaussianCoefficient
      D.triplet.levyMeasure →
    DriftsToPositiveInfinity P D.X →
    ∀ n : ℕ, 2 ≤ n →
      (ContDiffOn ℝ n (W 0) (Set.Ioi (0 : ℝ)) ↔
        HasSmoothJumpTail D.triplet.levyMeasure (n - 1))


def exercise8_4_iii : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    HasBoundedVariationTriplet D.gaussianCoefficient
      D.triplet.levyMeasure →
    ∀ q : ℝ, (0 < q ∨ (q = 0 ∧
        DriftsToNegativeInfinity P D.X)) →
      (ContDiffOn ℝ 1 (W q) (Set.Ioi (0 : ℝ)) ↔
        HasAtomlessNegativeLevyMeasure D.triplet.levyMeasure) ∧
      (∀ n : ℕ, 2 ≤ n →
        (ContDiffOn ℝ n (W q) (Set.Ioi (0 : ℝ)) ↔
          HasSmoothJumpTail D.triplet.levyMeasure (n - 1)))


def Oscillates {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂P,
    Filter.limsup (fun t : ℝ≥0 => (X t ω : EReal))
      Filter.atTop = ⊤ ∧
    Filter.liminf (fun t : ℝ≥0 => (X t ω : EReal))
      Filter.atTop = ⊥


def exercise8_4_iv : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    HasBoundedVariationTriplet D.gaussianCoefficient
      D.triplet.levyMeasure →
    Oscillates P D.X →
    (ContDiffOn ℝ 1 (W 0) (Set.Ioi (0 : ℝ)) ↔
      HasAtomlessNegativeLevyMeasure D.triplet.levyMeasure) ∧
    (∀ n : ℕ, 2 ≤ n →
      (ContDiffOn ℝ n (W 0) (Set.Ioi (0 : ℝ)) ↔
        HasSmoothJumpTail D.triplet.levyMeasure (n - 1)))

def exercise8_4 : Prop :=
  exercise8_4_i ∧ exercise8_4_ii ∧
  exercise8_4_iii ∧ exercise8_4_iv





def HasEsscherCoefficientLimit (ψ : ℝ → ℝ) (c : ℝ) : Prop :=
  ∃ L : ℝ,
    Filter.Tendsto
      (fun h : ℝ => h / (Phi ψ (h + ψ c) - c))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L)


noncomputable def esscherDownCoefficient
    (ψ : ℝ → ℝ) (c p : ℝ) : ℝ :=
  if p = ψ c then
    Classical.epsilon (fun L : ℝ =>
      Filter.Tendsto
        (fun h : ℝ => h / (Phi ψ (h + ψ c) - c))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L))
  else (p - ψ c) / (Phi ψ p - c)


def HasFiniteRightSlopeAt (ψ : ℝ → ℝ) (c : ℝ) : Prop :=
  ∃ d : ℝ,
    Filter.Tendsto
      (fun h : ℝ => (ψ (c + h) - ψ c) / h)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds d)


noncomputable def selectedRightSlope
    (ψ : ℝ → ℝ) (c : ℝ) : ℝ :=
  Classical.epsilon (fun d : ℝ =>
    Filter.Tendsto
      (fun h : ℝ => (ψ (c + h) - ψ c) / h)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds d))


noncomputable def downEsscherPayoff
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (p c x : ℝ) (ω : Ω) : ℝ :=
  match tauMinus X (-x) ω with
  | ⊤ => 0
  | (t : ℝ≥0) =>
      Real.exp (-p * (t : ℝ) + c * (X t ω + x))


noncomputable def hitTwoTimePayoff
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (p u x : ℝ) (ω : Ω) : ℝ :=
  match hitNegative X x ω with
  | ⊤ => 0
  | (t : ℝ≥0) =>
      match tauMinus X (-x) ω with
      | ⊤ => 0
      | (s : ℝ≥0) =>
          Real.exp (-p * (t : ℝ) - u * ((t : ℝ) - (s : ℝ)))


noncomputable def downOvershootAtNegativeLevel
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (ψ : ℝ → ℝ) (p u x : ℝ) (ω : Ω) : ℝ :=
  match tauMinus X (-x) ω with
  | ⊤ => 0
  | (t : ℝ≥0) =>
      Real.exp (-p * (t : ℝ) +
        Phi ψ (p+u) * (X t ω + x))


def exercise8_7_i : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (c q : ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    0 ≤ c → 0 ≤ q →
    Phi (shiftedExponent ψ c) q =
      Phi ψ (q + ψ c) - c


def exercise8_7_ii : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ (x c p : ℝ), 0 < x → 0 ≤ c → 0 ≤ p →
      let q := p - ψ c
      let V := tiltedScale c (W p)
      (∫ ω, downEsscherPayoff D.X p c x ω ∂P) =
        Real.exp (c * x) *
          (Zscale q V x -
            esscherDownCoefficient ψ c p * V x) ∧
      (p = ψ c →
        HasEsscherCoefficientLimit ψ c)


def exercise8_7_iii : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    ∀ (p u x : ℝ), 0 ≤ p → 0 ≤ u → 0 < x →
      (∫ ω, hitTwoTimePayoff D.X p u x ω ∂P) =
        ∫ ω, downOvershootAtNegativeLevel D.X ψ p u x ω ∂P


def exercise8_7_iv : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ p : ℝ, 0 ≤ p →
      HasFiniteRightSlopeAt ψ (Phi ψ p) ∧
      (∀ x : ℝ, 0 < x →
        (∫ ω, discountedAt p (hitNegative D.X x ω) ∂P) =
          Real.exp (Phi ψ p * x) -
            selectedRightSlope ψ (Phi ψ p) * W p x) ∧
      (HasBoundedVariationTriplet
        D.gaussianCoefficient D.triplet.levyMeasure →
        (∫ ω, discountedAt p (hitNegative D.X 0 ω) ∂P) =
          1 - selectedRightSlope ψ (Phi ψ p) /
            bvDrift D.triplet.drift D.triplet.levyMeasure) ∧
      (¬ HasBoundedVariationTriplet
        D.gaussianCoefficient D.triplet.levyMeasure →
        (∫ ω, discountedAt p (hitNegative D.X 0 ω) ∂P) = 1)

def exercise8_7 : Prop :=
  exercise8_7_i ∧ exercise8_7_ii ∧
  exercise8_7_iii ∧ exercise8_7_iv


def IsStandardBrownian {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω)
    (B : ℝ≥0 → Ω → ℝ) : Prop :=
  ProbabilityTheory.IsLevyProcess B P ∧
  (∀ᵐ ω ∂P,
    B 0 ω = 0 ∧ Continuous (fun t : ℝ≥0 => B t ω)) ∧
  ∀ (t : ℝ≥0) (ξ : ℝ),
    charFun (P.map (B t)) ξ =
      Complex.exp ((-((t : ℝ) * ξ ^ 2 / 2) : ℂ))


def IsHalfStableSubordinator {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω)
    (S : ℝ≥0 → Ω → ℝ) : Prop :=
  ProbabilityTheory.IsLevyProcess S P ∧
  (∀ᵐ ω ∂P,
    S 0 ω = 0 ∧ Monotone (fun t : ℝ≥0 => S t ω)) ∧
  ∀ (t : ℝ≥0) (β : ℝ), 0 ≤ β →
    (∫ ω, Real.exp (-β * S t ω) ∂P) =
      Real.exp (-(t : ℝ) * Real.sqrt (2 * β))


def BrownianDiagonalContact {Ω : Type*}
    (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : Prop :=
  ∃ t : ℝ≥0, 0 < t ∧
    B t ω = runningSup B t ω ∧ B t ω = (t : ℝ)


def exercise8_8_i : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B S : ℝ≥0 → Ω → ℝ),
    IsStandardBrownian P B →
    IsHalfStableSubordinator P S →
    (P {ω | BrownianDiagonalContact B ω}).toReal =
      (P {ω | hitNegative
        (fun t ω => (t : ℝ) - S t ω) 0 ω ≠ ⊤}).toReal


def exercise8_8_ii : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ),
    IsStandardBrownian P B →
    (P {ω | BrownianDiagonalContact B ω}).toReal = (1 / 2 : ℝ)

def exercise8_8 : Prop :=
  exercise8_8_i ∧ exercise8_8_ii





def HasIndependentCompetingLevyComponents
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (C : CompetingRiskPathData Ω n)
    (D : SpectrallyNegativeModel Ω P)
    (triples : Fin n → ProbabilityTheory.LevyKhintchineTriple) : Prop :=
  C.total = D.X ∧
  (∀ i : Fin n,
    ProbabilityTheory.IsLevyProcess (C.component i) P ∧
    (triples i).levyMeasure (Set.Ici (0 : ℝ)) = 0 ∧
    ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (C.component i t)) ξ =
        Complex.exp (((t : ℝ) : ℂ) *
          Kyprianou.Ch01.levyTripleExponent (triples i) ξ)) ∧
  (∀ (m : ℕ) (times : Fin m → ℝ≥0)
    (A : Fin n → Set (Fin m → ℝ)),
    (∀ i, MeasurableSet (A i)) →
    P {ω | ∀ i : Fin n,
      (fun j : Fin m => C.component i (times j) ω) ∈ A i} =
    ∏ i : Fin n,
      P {ω | (fun j : Fin m =>
        C.component i (times j) ω) ∈ A i})


noncomputable def preAtPassage
    {Ω : Type*}
    (X : ℝ≥0 → Ω → ℝ) (τ : WithTop ℝ≥0)
    (ω : Ω) : ℝ :=
  Classical.epsilon (fun v : ℝ => IsPrePassageValue X τ ω v)


def RuinedByComponent
    {Ω : Type*} (n : ℕ)
    (C : CompetingRiskPathData Ω n)
    (i : Fin n) (x : ℝ) (ω : Ω) : Prop :=
  ∃ (t : ℝ≥0) (valueBefore valueAfter componentBefore : ℝ),
    (t : WithTop ℝ≥0) = tauMinus (shifted C.total x) 0 ω ∧
    IsPrePassageValue (shifted C.total x)
      (tauMinus (shifted C.total x) 0 ω) ω valueBefore ∧
    postPassageValue (shifted C.total x)
      (tauMinus (shifted C.total x) 0 ω) ω = some valueAfter ∧
    IsPrePassageValue (C.component i)
      (tauMinus (shifted C.total x) 0 ω) ω componentBefore ∧
    valueAfter = valueBefore +
      (C.component i t ω - componentBefore) ∧
    valueAfter < valueBefore


def ComponentClaimPrePost
    {Ω : Type*} (n : ℕ)
    (C : CompetingRiskPathData Ω n)
    (i : Fin n) (x : ℝ)
    (A : Set (ℝ × ℝ)) (ω : Ω) : Prop :=
  let X := shifted C.total x
  let τ := tauMinus X 0 ω
  RuinedByComponent n C i x ω ∧
    (preAtPassage X τ ω,
      (postPassageValue X τ ω).getD 0) ∈ A


def exercise8_9_i : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (n : ℕ)
    (C : CompetingRiskPathData Ω n)
    (triples : Fin n → ProbabilityTheory.LevyKhintchineTriple)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ),
    HasIndependentCompetingLevyComponents P n C D triples →
    DriftsToPositiveInfinity P D.X →
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ (i : Fin n) (x : ℝ), 0 ≤ x →
      ∀ A : Set (ℝ × ℝ), MeasurableSet A →
        P {ω | ComponentClaimPrePost n C i x A ω} =
          ∫⁻ y in Set.Ici (0 : ℝ),
            ENNReal.ofReal
              (killedHalflineDensity ψ 0 (W 0) x y) *
              (triples i).levyMeasure
                {jump | (y, y + jump) ∈ A ∧ y + jump < 0}
              ∂volume


def exercise8_9_ii : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (n : ℕ)
    (C : CompetingRiskPathData Ω n)
    (triples : Fin n → ProbabilityTheory.LevyKhintchineTriple),
    HasIndependentCompetingLevyComponents P n C D triples →
    (∀ i : Fin n, HasBoundedVariationTriplet
      ((triples i).gaussianVariance : ℝ)
      (triples i).levyMeasure) →
    DriftsToPositiveInfinity P D.X →
    let d := bvDrift D.triplet.drift D.triplet.levyMeasure
    0 < d ∧
    ∀ (i : Fin n) (A : Set (ℝ × ℝ)),
      MeasurableSet A →
      P {ω | ComponentClaimPrePost n C i 0 A ω} =
        ∫⁻ y in Set.Ici (0 : ℝ),
          ENNReal.ofReal ((d)⁻¹) *
            (triples i).levyMeasure
              {jump | (y, y + jump) ∈ A ∧ y + jump < 0}
            ∂volume


def exercise8_9_iii : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (n : ℕ)
    (C : CompetingRiskPathData Ω n)
    (triples : Fin n → ProbabilityTheory.LevyKhintchineTriple),
    HasIndependentCompetingLevyComponents P n C D triples →
    (∀ i : Fin n, HasBoundedVariationTriplet
      ((triples i).gaussianVariance : ℝ)
      (triples i).levyMeasure ∧
      Integrable (C.component i 1) P) →
    DriftsToPositiveInfinity P D.X →
    let d := bvDrift D.triplet.drift D.triplet.levyMeasure
    0 < d ∧
    ∀ i : Fin n,
      (P {ω | RuinedByComponent n C i 0 ω}).toReal =
        (bvDrift (triples i).drift (triples i).levyMeasure -
          ∫ ω, C.component i 1 ω ∂P) / d

def exercise8_9 : Prop :=
  exercise8_9_i ∧ exercise8_9_ii ∧ exercise8_9_iii





def IsEsscherLaplaceShifted
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ (β : ℝ) (t : ℝ≥0),
    0 ≤ β → 0 < t →
    Integrable (fun ω => Real.exp ((c + β) * D.X t ω)) P →
    (∫ ω,
      Real.exp (β * D.X t ω) *
        esscherDensity (SpectrallyNegativeModel.toData P D)
          ψ c t ω ∂P) =
      Real.exp ((t : ℝ) * shiftedExponent ψ c β)


def result8_4 : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ),
    IsFullMomentLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ c : ℝ,
      Integrable (fun ω => Real.exp (c * D.X 1 ω)) P →
      HasLawfulEsscherDensities
        (SpectrallyNegativeModel.toData P D) ψ c ∧
      IsEsscherLaplaceShifted P D ψ c ∧
      ∃ (F G : ℂ → ℝ → ℂ),
        (∀ x : ℝ, 0 ≤ x →
          Differentiable ℂ (fun q : ℂ => F q x) ∧
          Differentiable ℂ (fun q : ℂ => G q x)) ∧
        (∀ (q x : ℝ), 0 ≤ q → 0 ≤ x →
          F (q : ℂ) x = (W q x : ℂ)) ∧
        (∀ (p x : ℝ), 0 ≤ p → 0 ≤ x →
          0 ≤ p + ψ c →
          G (p : ℂ) x =
            ((tiltedScale c (W (p + ψ c)) x) : ℂ)) ∧
        (∀ (q : ℂ) (x : ℝ), 0 ≤ x →
          F q x =
            Complex.exp (((c * x : ℝ) : ℂ)) *
              G (q - ((ψ c : ℝ) : ℂ)) x)





def NoDrawdownBeforeUpcrossing {Ω : Type*}
    (X : ℝ≥0 → Ω → ℝ)
    (a h : ℝ) (ω : Ω) : Prop :=
  ∀ t : ℝ≥0,
    (t : WithTop ℝ≥0) < tauPlus X a ω →
      reflectAtSup X 0 t ω < h


def HasActualQExcursionHeightLaw {Ω : Type}
    [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (q : ℝ)
    (n : Measure ℝ) : Prop :=
  PhiIsLargestRoot ψ q ∧
  ∀ (a h : ℝ), 0 < a → 0 < h →
    n (Set.Ici h) < ⊤ ∧
    (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X a h ω},
      Real.exp (Phi ψ q * a) *
        discountedAt q (tauPlus D.X a ω) ∂P) =
      Real.exp (-a * (n (Set.Ici h)).toReal)


def HasQExcursionScaleRepresentation
    (ψ : ℝ → ℝ) (q : ℝ)
    (W : ℝ → ℝ) (n : Measure ℝ) : Prop :=
  (∀ x : ℝ, 0 < x → 0 < W x) ∧
  ∀ (x a : ℝ), 0 < x → x < a →
    IntegrableOn
      (fun t : ℝ =>
        Phi ψ q + (n (Set.Ici t)).toReal)
      (Set.Icc x a) volume ∧
    W x = W a * Real.exp
      (-(∫ t in x..a,
          Phi ψ q + (n (Set.Ici t)).toReal))


def result8_2 : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ q : ℝ, 0 ≤ q →
      ∃ n : Measure ℝ,
        HasActualQExcursionHeightLaw P D ψ q n ∧
        HasQExcursionScaleRepresentation ψ q (W q) n ∧
        (∀ x : ℝ, 0 < x →
          ∃ dLeft dRight : ℝ,
            HasDerivWithinAt (W q) dLeft (Set.Iic x) x ∧
            HasDerivWithinAt (W q) dRight (Set.Ici x) x ∧
            dLeft =
              (Phi ψ q + (n (Set.Ici x)).toReal) * W q x ∧
            dRight =
              (Phi ψ q + (n (Set.Ioi x)).toReal) * W q x ∧
            (dLeft = dRight ↔ n {x} = 0)) ∧
        (ContDiffOn ℝ 1 (W q) (Set.Ioi (0 : ℝ)) ↔
          ∀ x : ℝ, 0 < x → n {x} = 0)







def technicalGOUConstruction : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (lambda : ℝ),
    0 < lambda → HasGOUConstruction P D lambda


def technicalGOUVersionUniqueness : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P],
    GOUVersionUniquenessObligation P


def technicalGOUExitInvariance : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P],
    GOUExitVersionLawObligation P


def technicalLawTripletIdentity : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P),
    HasLawTripletLaplaceBridge (SpectrallyNegativeModel.toData P D)


def technicalPhiRootDomain : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    ∀ q : ℝ, 0 ≤ q →
      IsScaleTransformDomainBridge ψ q


def technicalQExcursionHeightConstruction : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    ∀ q : ℝ, 0 ≤ q →
      ∃ n : Measure ℝ,
        HasActualQExcursionHeightLaw P D ψ q n


def technicalExtendedRightScaleSlope : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ q : ℝ, 0 ≤ q →
      ∃ d : EReal, HasExtendedRightSlope (W q) d


def technicalTwoSidedStorage : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (x c : ℝ), 0 ≤ x → x ≤ c → 0 < c →
      HasUniqueCappedStorage P D.X x c


def technicalGOUPositiveHDomain : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (lambda a y theta : ℝ),
    0 < lambda → 0 < a → y ≤ a → 0 < theta →
    GOUHasLogJumpIntegrability D.triplet.levyMeasure →
    (¬ HasBoundedVariationTriplet
      D.gaussianCoefficient D.triplet.levyMeasure ∨
      (HasBoundedVariationTriplet
        D.gaussianCoefficient D.triplet.levyMeasure ∧
        lambda * a <
          bvDrift D.triplet.drift D.triplet.levyMeasure)) →
    IsGOUPositiveHDomain
      (tripletLaplace D.triplet.drift
        D.gaussianCoefficient D.triplet.levyMeasure)
      lambda theta y a


def technicalGOUZeroHBoundary : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (M : GOUInput Ω P) (lambda a y : ℝ),
    0 < lambda → 0 < a → y ≤ a →
    M.driver = D → M.meanReversion = lambda →
    GOUHasLogJumpIntegrability D.triplet.levyMeasure →
    (¬ HasBoundedVariationTriplet
      D.gaussianCoefficient D.triplet.levyMeasure ∨
      (HasBoundedVariationTriplet
        D.gaussianCoefficient D.triplet.levyMeasure ∧
        lambda * a <
          bvDrift D.triplet.drift D.triplet.levyMeasure)) →
    IsGOUZeroHBoundary
      (tripletLaplace D.triplet.drift
        D.gaussianCoefficient D.triplet.levyMeasure)
      lambda y a
      (∫ ω, discountedAt 0 (GOUExit M y a ω) ∂P)


def technicalCappedStorageVersionInvariance : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : ℝ≥0 → Ω → ℝ) (x c q : ℝ),
    0 < x → x < c → 0 < q →
    (∀ᵐ ω ∂P, ∀ t : ℝ≥0, X t ω = Y t ω) →
    ∀ (S : CappedStorage P X x c)
      (T : CappedStorage P Y x c),
      (∫ ω, discountedAt q (cappedEmptyingTime S ω) ∂P) =
      (∫ ω, discountedAt q (cappedEmptyingTime T ω) ∂P)


def technicalFullMomentExponentExistence : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P),
    ∃ ψ : ℝ → ℝ,
      IsFullMomentLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ


def technicalEsscherDensityConsistency : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (c : ℝ),
    IsFullMomentLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    Integrable (fun ω => Real.exp (c * D.X 1 ω)) P →
    HasLawfulEsscherDensities (SpectrallyNegativeModel.toData P D) ψ c


def technicalZeroDenominatorReflectedExit : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsFullMomentLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ (θ x a : ℝ), 0 < a → 0 ≤ x → x ≤ a →
    Integrable (fun ω => Real.exp (θ * D.X 1 ω)) P →
    let V := tiltedScale θ (W 0)
    HasDerivWithinAt V (derivWithin V (Set.Ici a) a)
      (Set.Ici a) a →
    derivWithin V (Set.Ici a) a + θ * V a = 0 →
    (∫ ω, reflectedSupJointPayoff D.X 0 θ x a ω ∂P) = 0


def technicalZeroDerivativeReflectedPotential : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ (q x a : ℝ), 0 ≤ q → 0 < a → 0 ≤ x → x < a →
    derivWithin (W q) (Set.Ici a) a = 0 →
    ∀ U : Measure ℝ,
      IsSupremumReflectedPotential P D.X q x a U →
      q = 0 ∧ U {0} = ⊤ ∧
      (∀ n : ℕ,
        0 < derivWithin
          (W (1 / (((n + 1 : ℕ) : ℝ))))
          (Set.Ici a) a) ∧
      ∀ A : Set ℝ, MeasurableSet A →
        U A =
          ⨆ n : ℕ,
            (supremumReflectedScaleResolvent W
              (1 / (((n + 1 : ℕ) : ℝ))) x a) A







def sourceCertificate_result8_1 : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P),
      ∃ (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ),
        IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ ∧
        HasSourceScaleFamily ψ W ∧
        (∀ (q x : ℝ), 0 < q →
          downExpectation P D.X q x =
            Zscale q (W q) x -
              q / Phi ψ q * W q x) ∧
        (∀ (x : ℝ) (d : ℝ),
          HasPositiveFiniteRightPsiSlope ψ d →
          downExpectation P D.X 0 x = 1 - d * W 0 x) ∧
        ((¬ ∃ d : ℝ, HasPositiveFiniteRightPsiSlope ψ d) →
          ∀ x : ℝ, downExpectation P D.X 0 x = 1) ∧
        (∀ (q x a : ℝ), 0 ≤ q → 0 < a → x ≤ a →
          0 < W q a ∧
          upBeforeDownExpectation P D.X q x a =
            W q x / W q a ∧
          downBeforeUpExpectation P D.X q x a =
            Zscale q (W q) x -
              Zscale q (W q) a * W q x / W q a)


def sourceCertificate_result8_2 : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P)
      (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ q : ℝ, 0 ≤ q →
        ∃ n : Measure ℝ,
          HasActualQExcursionHeightLaw P D ψ q n ∧
          HasQExcursionScaleRepresentation ψ q (W q) n ∧
          (∀ x : ℝ, 0 < x →
            ∃ dLeft dRight : ℝ,
              HasDerivWithinAt (W q) dLeft (Set.Iic x) x ∧
              HasDerivWithinAt (W q) dRight (Set.Ici x) x ∧
              dLeft =
                (Phi ψ q + (n (Set.Ici x)).toReal) * W q x ∧
              dRight =
                (Phi ψ q + (n (Set.Ioi x)).toReal) * W q x ∧
              (dLeft = dRight ↔ n {x} = 0)) ∧
          (ContDiffOn ℝ 1 (W q) (Set.Ioi (0 : ℝ)) ↔
            ∀ x : ℝ, 0 < x → n {x} = 0)


def sourceCertificate_result8_3 : Prop :=
  ∀ (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ),
      HasSourceScaleFamily ψ W →
      ∀ x : ℝ, 0 ≤ x →
        ∃ F : ℂ → ℂ,
          Differentiable ℂ F ∧
          ∀ q : ℝ, 0 ≤ q → F (q : ℂ) = (W q x : ℂ)


def sourceCertificate_result8_4 : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P)
      (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ),
      IsFullMomentLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ c : ℝ,
        Integrable (fun ω => Real.exp (c * D.X 1 ω)) P →
        HasLawfulEsscherDensities
          (SpectrallyNegativeModel.toData P D) ψ c ∧
        IsEsscherLaplaceShifted P D ψ c ∧
        ∃ (F G : ℂ → ℝ → ℂ),
          (∀ x : ℝ, 0 ≤ x →
            Differentiable ℂ (fun q : ℂ => F q x) ∧
            Differentiable ℂ (fun q : ℂ => G q x)) ∧
          (∀ (q x : ℝ), 0 ≤ q → 0 ≤ x →
            F (q : ℂ) x = (W q x : ℂ)) ∧
          (∀ (p x : ℝ), 0 ≤ p → 0 ≤ x →
            0 ≤ p + ψ c →
            G (p : ℂ) x =
              ((tiltedScale c (W (p + ψ c)) x) : ℂ)) ∧
          (∀ (q : ℂ) (x : ℝ), 0 ≤ x →
            F q x =
              Complex.exp (((c * x : ℝ) : ℂ)) *
                G (q - ((ψ c : ℝ) : ℂ)) x)


def sourceCertificate_result8_5 : Prop :=
  ∀ (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ),
      HasSourceScaleFamily ψ W →
      ∀ x : ℝ, 0 < x →
        ∃ F : ℂ → ℂ,
          Differentiable ℂ F ∧
          ∀ q : ℝ, 0 ≤ q → F (q : ℂ) = (Zscale q (W q) x : ℂ)


def sourceCertificate_result8_6 : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ q : ℝ, 0 ≤ q →
        ((W q 0 = 0) ↔
          ¬ HasBoundedVariationTriplet
              D.gaussianCoefficient D.triplet.levyMeasure) ∧
        (HasBoundedVariationTriplet
          D.gaussianCoefficient D.triplet.levyMeasure →
          0 < bvDrift D.triplet.drift D.triplet.levyMeasure ∧
          W q 0 = (bvDrift D.triplet.drift D.triplet.levyMeasure)⁻¹)


def sourceCertificate_result8_7 : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q a x : ℝ), 0 ≤ q → 0 < a → 0 ≤ x → x ≤ a →
        ∃ U : Measure ℝ,
          IsIntervalKilledResolvent P (shifted D.X x) q a U ∧
          U = (volume.restrict (Set.Icc 0 a)).withDensity
            (fun y : ℝ =>
              ENNReal.ofReal (killedIntervalDensity (W q) a x y))


def sourceCertificate_result8_8 : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q x : ℝ), 0 ≤ q → 0 ≤ x →
        ∃ U : Measure ℝ,
          IsHalflineKilledResolvent P (shifted D.X x) q U ∧
          U = (volume.restrict (Set.Ici 0)).withDensity
            (fun y : ℝ =>
              ENNReal.ofReal (killedHalflineDensity ψ q (W q) x y))


def sourceCertificate_result8_9 : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q x : ℝ), 0 < q →
        DifferentiableAt ℝ (Phi ψ) q ∧
        ∃ U : Measure ℝ,
          IsResolvent P (shifted D.X x) q U ∧
          U = volume.withDensity
            (fun y : ℝ =>
              ENNReal.ofReal
                (unrestrictedPotentialDensity ψ q (W q) (x-y)))


def sourceCertificate_result8_10 : Prop :=
  result8_10_i ∧ result8_10_ii


def sourceCertificate_result8_11 : Prop :=
  result8_11_i ∧ result8_11_ii


def sourceCertificate_result8_12 : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P)
      (reversion a y : ℝ),
      0 < reversion → 0 < a → y ≤ a →
      GOUHasLogJumpIntegrability D.triplet.levyMeasure →
      (¬ HasBoundedVariationTriplet D.gaussianCoefficient D.triplet.levyMeasure ∨
        (HasBoundedVariationTriplet D.gaussianCoefficient
           D.triplet.levyMeasure ∧
         reversion * a < bvDrift D.triplet.drift D.triplet.levyMeasure)) →
      HasGOUConstruction P D reversion ∧
      ∀ M : GOUInput Ω P,
        M.driver = D → M.meanReversion = reversion →
        IsGOUTheorem812TransformConclusion M
          (tripletLaplace D.triplet.drift
            D.gaussianCoefficient D.triplet.levyMeasure) y a


def sourceCertificate_exercise8_1 : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (F : Filtration ℝ≥0 mΩ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasCompletedNaturalFiltration P D F →
      HasNegativeRightPsiSlope ψ →
      ∀ (t : ℝ≥0) (A : Set Ω),
        @MeasurableSet Ω (F t) A →
        Filter.Tendsto
          (fun a : ℝ =>
            (P (A ∩ {ω | tauPlus D.X a ω ≠ ⊤})).toReal /
              (P {ω | tauPlus D.X a ω ≠ ⊤}).toReal)
          Filter.atTop
          (nhds ((esscherFiniteTimeLaw
            (SpectrallyNegativeModel.toData P D) ψ
            (Phi ψ 0) t) A).toReal)


def sourceCertificate_exercise8_2 : Prop :=
  exercise8_2_i ∧ exercise8_2_ii ∧
    exercise8_2_iii ∧ exercise8_2_iv


def sourceCertificate_exercise8_3 : Prop :=
  exercise8_3_i ∧ exercise8_3_ii ∧ exercise8_3_iii


def sourceCertificate_exercise8_4 : Prop :=
  exercise8_4_i ∧ exercise8_4_ii ∧
    exercise8_4_iii ∧ exercise8_4_iv


def sourceCertificate_exercise8_5 : Prop :=
  exercise8_5_i ∧ exercise8_5_ii


def sourceCertificate_exercise8_6 : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ x : ℝ, x ≤ 0 →
        (D.gaussianCoefficient = 0 →
          (P {ω | postPassageValue D.X
            (tauMinus D.X x ω) ω = some x}).toReal = 0) ∧
        (0 < D.gaussianCoefficient ^ 2 →
          HasDerivWithinAt (W 0)
            (derivWithin (W 0) (Set.Ici (-x)) (-x))
            (Set.Ici (-x)) (-x) ∧
          (P {ω | postPassageValue D.X
            (tauMinus D.X x ω) ω = some x}).toReal =
            D.gaussianCoefficient ^ 2 / 2 *
              (derivWithin (W 0) (Set.Ici (-x)) (-x) -
                Phi ψ 0 * W 0 (-x)))


def sourceCertificate_exercise8_7 : Prop :=
  exercise8_7_i ∧ exercise8_7_ii ∧
    exercise8_7_iii ∧ exercise8_7_iv


def sourceCertificate_exercise8_8 : Prop :=
  exercise8_8_i ∧ exercise8_8_ii


def sourceCertificate_exercise8_9 : Prop :=
  exercise8_9_i ∧ exercise8_9_ii ∧ exercise8_9_iii


def sourceCertificate_exercise8_10 : Prop :=
  exercise8_10_i ∧ exercise8_10_ii ∧
    exercise8_10_iii ∧ exercise8_10_iv


def sourceCertificate_exercise8_11 : Prop :=
  exercise8_11_i ∧ exercise8_11_ii ∧ exercise8_11_iii


def sourceCertificate_exercise8_12 : Prop :=
  exercise8_12_i ∧ exercise8_12_ii



def chapterEightMain : Prop :=
  sourceCertificate_result8_1 ∧
  sourceCertificate_result8_2 ∧
  sourceCertificate_result8_3 ∧
  sourceCertificate_result8_4 ∧
  sourceCertificate_result8_5 ∧
  sourceCertificate_result8_6 ∧
  sourceCertificate_result8_7 ∧
  sourceCertificate_result8_8 ∧
  sourceCertificate_result8_9 ∧
  sourceCertificate_result8_10 ∧
  sourceCertificate_result8_11 ∧
  sourceCertificate_result8_12 ∧
  sourceCertificate_exercise8_1 ∧
  sourceCertificate_exercise8_2 ∧
  sourceCertificate_exercise8_3 ∧
  sourceCertificate_exercise8_4 ∧
  sourceCertificate_exercise8_5 ∧
  sourceCertificate_exercise8_6 ∧
  sourceCertificate_exercise8_7 ∧
  sourceCertificate_exercise8_8 ∧
  sourceCertificate_exercise8_9 ∧
  sourceCertificate_exercise8_10 ∧
  sourceCertificate_exercise8_11 ∧
  sourceCertificate_exercise8_12

end Kyprianou.Ch08.StageB

namespace Kyprianou.Ch08.StageB

/-- Explicitly OPEN source obligation; proof is not submitted. -/
theorem open_technicalPhiRootDomain : technicalPhiRootDomain := by
  sorry

end Kyprianou.Ch08.StageB
