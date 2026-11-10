-- Prove2me | Theorems.Thm_OAI_InitialMeanSquare_initial_nonzero_source_norm_le_squarefree_bins
-- name    : OAI.InitialMeanSquare.initial_nonzero_source_norm_le_squarefree_bins
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T22:34:57.873061+00:00
-- url     : https://prove2.me/theorems/263ccf09-149f-4081-adeb-855f29172e90
-- title:
--   Initial Mean Square: initial nonzero source norm le squarefree bins
-- statement:
--   The Initial Mean Square construction uses the initial nonzero source norm le squarefree bins property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/DiagonalDensity.lean#L381-L412
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/DiagonalDensity.lean#L381-L412

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CompletedDyadicRows
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_DiagonalDensity
set_option autoImplicit false
open OAI
noncomputable section
open OAI.InitialMeanSquare
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration
open FirstPassCubeLabels (normalizedColumn columnLog)

theorem OAI.InitialMeanSquare.initial_nonzero_source_norm_le_squarefree_bins
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda^2 ∣ p i-1) (F : Finset ι) (Ψ : O →* ℂ) (m : O)
    (g W : 𝓢(ℝ,ℂ)) (Z H M Kmax : ℝ) (hZ : 0 < Z)
    (hgM : ∀ t, g t ≠ 0 → |t| ≤ M)
    (K : Finset ι → Finset ι → Finset O)
    (hK : ∀ R ∈ F.powerset, ∀ x ∈ secondSupportedSector p F K R Z M,
      elementNorm (sourceObservation p x).1 ≤ Kmax) :
    let G := fun S => normalizedColumn p (fun T => g (columnLog p Z T)) S
    ‖truncatedSecondSource p hp hg hinj F Ψ m 1 1 G W H (fun C E => (K C E).erase 0)‖ ≤
      ∑ ray : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p F (Z*Real.exp M),
        ∑ j ∈ secondLogBinBox (Z*Real.exp M) Kmax,
          ‖secondExpansionSource p hp hcop hg F Ψ m 1 1 ray
            (initialSquarefreeSector p (secondLogSector p ∅ F K R Z M j)) G G W H‖ := by sorry
