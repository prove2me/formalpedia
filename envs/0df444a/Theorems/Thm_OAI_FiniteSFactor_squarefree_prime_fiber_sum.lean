-- Prove2me | Theorems.Thm_OAI_FiniteSFactor_squarefree_prime_fiber_sum
-- name    : OAI.FiniteSFactor.squarefree_prime_fiber_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:15:16.109543+00:00
-- url     : https://prove2.me/theorems/077bb423-0823-4781-836b-c179c2d12f31
-- title:
--   Finite SFactor: squarefree prime fiber sum
-- statement:
--   The Finite SFactor construction uses the squarefree prime fiber sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/PrimeExtraction.lean#L154-L196
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/PrimeExtraction.lean#L154-L196

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

theorem OAI.FiniteSFactor.squarefree_prime_fiber_sum (P : Ideal O) (hP : Prime P)
    (m : ℕ) (w : Ideal O → ℂ) :
    (∑ I ∈ badFiber P m, w I) =
      ∑ J ∈ goodFiber P m, w (P * J) := by sorry
