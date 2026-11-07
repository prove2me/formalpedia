-- Prove2me | Theorems.Thm_OAI_ShortDraftHeckeBridge_norm_prime_implies_over
-- name    : OAI.ShortDraftHeckeBridge.norm_prime_implies_over
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:52:45.584265+00:00
-- url     : https://prove2.me/theorems/ee9c3d82-1ffa-4206-9e56-351c36a0b317
-- title:
--   Short Draft Hecke Bridge: norm prime implies over
-- statement:
--   The Short Draft Hecke Bridge construction uses the norm prime implies over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/NormFiberCharacters.lean#L290-L301
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/NormFiberCharacters.lean#L290-L301

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_NormFiberMellin
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_NormFiberCharacters
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
open OAI.ShortDraftHeckeBridge

theorem OAI.ShortDraftHeckeBridge.norm_prime_implies_over {p : ℕ} (hp : p.Prime) (I : Ideal O)
    (hI : Ideal.absNorm I = p) :
    I ∈ (Ideal.span {(p : ℤ)}).primesOver O := by sorry
