-- Prove2me | Theorems.Thm_OAI_CanonicalRowCompletion_progressingCanonicalFamily_energy
-- name    : OAI.CanonicalRowCompletion.progressingCanonicalFamily_energy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:48:42.302958+00:00
-- url     : https://prove2.me/theorems/e4daea22-a88b-4d0e-9078-e1d61b090055
-- title:
--   Canonical Row Completion: progressing Canonical Family energy
-- statement:
--   The Canonical Row Completion construction uses the progressing Canonical Family energy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/FredholmAlternative.lean#L560-L633
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/FredholmAlternative.lean#L560-L633

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ClosedRecursion
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_FredholmAlternative
import Theorems.Thm_OAI_CanonicalQuadraticSieve_poolPrimary_coprime

set_option autoImplicit false
open OAI
noncomputable section
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
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
open OAI.CanonicalRowCompletion
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalCubeSeparation JointLogSeparation
open FirstPassCubeLabels (columnLog)

theorem OAI.CanonicalRowCompletion.progressingCanonicalFamily_energy
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O) (W : ℝ→ℂ)
    (a b : ℝ) (ha : 0<a) (hb : 0≤b)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W)
    (V : 𝓢(ℝ,ℂ)) (hV : ∀u,|u|≤columnWindowRadius a b→V u=1)
    (X H₀ K E oldHeight : ℝ) (J : ℕ)
    (hX : 0<X) (hK : 0<K) (hE : 0≤E) (hD : b*X≤D) :
    let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    let β:=fun I v=>reopenedCubeCoefficient H₀
      (rowTwist (normHeightTwist Ψ oldHeight) (m*excludedGenerator S) (idealGenerator I) 1) (cubeIdeal F v)
    let n:=fun v=>(Ideal.absNorm (cubeIdeal F v):ℝ)
    (∀j∈cubeLogRange b X,
      let B:=normLogScale j
      let Q':=progressingCubes S D H₀ (activeCubeLogBin S D b X j)
      Q'.Nonempty → ∀ξ : ℝ,B*rowFamilyEnergy labels (fun I z=>
        reopenedCanonicalRow (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
          (poolPrimary_good F hF) Finset.univ Q' (separatedCubeCoefficient (β I) n B ξ)
          Ψ m (idealGenerator I)
          (fun T=>frequencyTwist V (oldHeight+ξ) (columnLog (poolPrimary F) (X/B^3) T)) z) K≤
        E*(1+|oldHeight+ξ|)^(2*J)) →
    rowFamilyEnergy labels (fun I z=>outsideCanonicalRow S D hbad (normHeightTwist Ψ oldHeight)
      m (idealGenerator I) z W X) K≤
    2*X*rowFamilyEnergy labels (fun I z=>
      shortCompletedSum (rowTwist (normHeightTwist Ψ oldHeight) (m*excludedGenerator S) (idealGenerator I) z) W X H₀) K+
    2*((cubeLogRange b X).card:ℝ)^2*E*(1+|oldHeight|)^(2*J)*
      (∫ξ : ℝ,‖reopeningCoefficient W a b ha hs hW ξ‖*(1+|ξ|)^J)^2 := by sorry
