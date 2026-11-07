-- Prove2me | Theorems.Thm_OAI_FiniteSFactor_outsideWeight_mul
-- name    : OAI.FiniteSFactor.outsideWeight_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:15:26.64012+00:00
-- url     : https://prove2.me/theorems/3c0b13d6-5bc1-4e59-8085-c763acdb400a
-- title:
--   Finite SFactor: outside Weight mul
-- statement:
--   The Finite SFactor construction uses the outside Weight mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/PrimeExtraction.lean#L87-L114
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/PrimeExtraction.lean#L87-L114

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_LocalEulerIdentities
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
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
open OAI.FiniteSFactor

theorem OAI.FiniteSFactor.outsideWeight_mul (S : Finset (Ideal O))
    (hprime : ∀ P ∈ S, Prime P) (w : Ideal O → ℂ)
    (I J : Ideal O) (hweight : w (I * J) = w I * w J) :
    outsideWeight S w (I * J) =
      outsideWeight S w I * outsideWeight S w J := by sorry
