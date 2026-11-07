-- Prove2me | Theorems.Thm_OAI_ConcretePrimeRowBridge_outsideCoeff_prime_extraction_with_constants
-- name    : OAI.ConcretePrimeRowBridge.outsideCoeff_prime_extraction_with_constants
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:20:10.643605+00:00
-- url     : https://prove2.me/theorems/5979d991-fead-4a2c-aa93-77e57258926f
-- title:
--   Concrete Prime Row Bridge: outside Coeff prime extraction with constants
-- statement:
--   The Concrete Prime Row Bridge construction uses the outside Coeff prime extraction with constants property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/PrimeRows/NormFiberExtraction.lean#L578-L646
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/PrimeRows/NormFiberExtraction.lean#L578-L646

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_NormFiberExtraction
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
open OAI.ConcretePrimeRowBridge
open ShortDraftHeckeBridge FiniteSFactor
open ShortDraftHeckeBridge FiniteSFactor Filter

theorem OAI.ConcretePrimeRowBridge.outsideCoeff_prime_extraction_with_constants
    {β : Type*} {q : ℕ}
    (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ)
    (S : Finset (Ideal O))
    (hSbad : ∀ P : Ideal O, P.IsMaximal → goodLambda ∈ P → P ∈ S)
    (hW : ∀ n, ‖W n‖ ≤ 1)
    (selected : Finset β) (p : β → O)
    (D H : ℕ) (ε : ℝ) (eta : ℝ) (Cmean Ccount : ℝ)
    (hD : 1 ≤ D) (hε : 0 ≤ ε) (heta : 0 ≤ eta)
    (hp : ∀ i ∈ selected, p i ≠ 0)
    (hprime : ∀ i ∈ selected, (Ideal.span {p i} : Ideal O).IsMaximal)
    (hinj : Set.InjOn (fun i => (Ideal.span {p i} : Ideal O)) (selected : Set β))
    (hnormlower : ∀ i ∈ selected,
      (D : ℝ) ^ (11 / 60 : ℝ) / 2 ≤
        (Ideal.absNorm (Ideal.span {p i}) : ℝ))
    (hnormupper : ∀ i ∈ selected,
      (Ideal.absNorm (Ideal.span {p i}) : ℝ) ≤
        (D : ℝ) ^ (11 / 60 : ℝ))
    (hH : Nat.floor ((D : ℝ) ^ (11 / 10 : ℝ)) ≤ H)
    (hcount : Ccount * (D : ℝ) ^ ((11 / 60 : ℝ) - ε) ≤
      (selected.card : ℝ))
    (hmean :
      (∑ u ∈ rowNormDisk H,
        ‖idealRowSum (outsideIdealsUpTo S D)
            (outsideIdealsUpTo_ne_bot S D)
            (outsideIdealsUpTo_good S D hSbad)
            χ W u‖ ^ 2) ≤
        Cmean * (D : ℝ) ^ ((21 / 10 : ℝ) + ε))
    (hmeanAbsorb : Cmean ≤ (D : ℝ) ^ eta)
    (hcountAbsorb : 1 ≤ Ccount * (D : ℝ) ^ eta) :
    ‖∑ n ∈ Finset.Icc 1 D,
        FiniteSFactor.outsideCoeff S (baseChangeWeight χ) n * W n‖ ≤
      384 * (D : ℝ) ^ ((23 / 24 : ℝ) + (ε + eta)) := by sorry
