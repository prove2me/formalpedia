-- Prove2me | Theorems.Thm_OAI_ShortDraftCRT_fixed_ray_completion_in_sector
-- name    : OAI.ShortDraftCRT.fixed_ray_completion_in_sector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:42:06.255572+00:00
-- url     : https://prove2.me/theorems/73fe25bf-f7c1-4cf3-8846-18f5270534c7
-- title:
--   Short Draft CRT: fixed ray completion in sector
-- statement:
--   The Short Draft CRT construction uses the fixed ray completion in sector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/ResidualCuspDecay.lean#L257-L278
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/ResidualCuspDecay.lean#L257-L278

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_BesselMellinTransform
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_TranslatedFourierResidues
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ResidualCuspDecay
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
open OAI.ShortDraftCRT
open scoped BigOperators Classical Matrix
variable {R : Type*} [CommRing R]
variable [IsDomain R]

theorem OAI.ShortDraftCRT.fixed_ray_completion_in_sector (M a c : R) (rows rows0 : List (R×R))
    (b0 d0 : R) (hc0 : c≠0) (hc : c∣M)
    (hbase : IsCoprime a c) (hrows : GoodRows c rows)
    (hr : IsCoprime (rows.map Prod.fst).prod (M*c))
    (hlift : ∀ph∈rows,M^2∣ph.2) (hlift0 : ∀ph∈rows0,M^2∣ph.2)
    (hsector : M^2∣(rows.map Prod.fst).prod-(rows0.map Prod.fst).prod)
    (hdet0 : crossNum a c rows0*d0-b0*crossDen c rows0=1) :
    ∃b d : R, crossNum a c rows*d-b*crossDen c rows=1 ∧ M*c∣d-d0 ∧
      (!![crossNum a c rows,b;crossDen c rows,d] : Matrix (Fin 2) (Fin 2) R).map
          (Ideal.Quotient.mk (Ideal.span {M})) =
        (!![crossNum a c rows0,b0;crossDen c rows0,d0] : Matrix (Fin 2) (Fin 2) R).map
          (Ideal.Quotient.mk (Ideal.span {M})) := by sorry
