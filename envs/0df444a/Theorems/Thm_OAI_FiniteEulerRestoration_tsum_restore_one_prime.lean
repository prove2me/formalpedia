-- Prove2me | Theorems.Thm_OAI_FiniteEulerRestoration_tsum_restore_one_prime
-- name    : OAI.FiniteEulerRestoration.tsum_restore_one_prime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:17:50.669072+00:00
-- url     : https://prove2.me/theorems/d43297e7-4330-4682-a85e-685b7ed9cf15
-- title:
--   Finite Euler Restoration: tsum restore one prime
-- statement:
--   The Finite Euler Restoration construction uses the tsum restore one prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/FiniteEulerRestoration.lean#L107-L148
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/FiniteEulerRestoration.lean#L107-L148

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_FiniteEulerRestoration
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
open OAI.FiniteEulerRestoration

theorem OAI.FiniteEulerRestoration.tsum_restore_one_prime {N : ℕ} (hN : 0 < N)
    (c : ℂ) (a b φ : ℕ → ℂ)
    (hcoeff : ∀ n, a n = b n + if N ∣ n then c * b (n / N) else 0)
    (hb : Summable (fun n => b n * φ n))
    (hshift : Summable (fun m => b m * φ (N * m))) :
    (∑' n : ℕ, a n * φ n) =
      (∑' n : ℕ, b n * φ n) +
        c * (∑' m : ℕ, b m * φ (N * m)) := by sorry
