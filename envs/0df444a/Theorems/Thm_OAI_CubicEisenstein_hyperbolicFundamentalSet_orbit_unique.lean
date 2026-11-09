-- Prove2me | Theorems.Thm_OAI_CubicEisenstein_hyperbolicFundamentalSet_orbit_unique
-- name    : OAI.CubicEisenstein.hyperbolicFundamentalSet_orbit_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T05:31:24.076204+00:00
-- url     : https://prove2.me/theorems/e78f9fcf-c3cf-4e50-a829-3072642af54d
-- title:
--   Cubic Eisenstein: hyperbolic Fundamental Set orbit unique
-- statement:
--   The Cubic Eisenstein construction uses the hyperbolic Fundamental Set orbit unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/FundamentalDomain.lean#L374-L380
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/FundamentalDomain.lean#L374-L380

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_GlobalBinLoss
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_FundamentalDomain
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicFrobenius_continuous
import Theorems.Thm_OAI_CubicEisenstein_quadraticHeightDenominator_continuous
attribute [local fun_prop] OAI.CubicEisenstein.quadraticHeightDenominator_continuous


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
open OAI.CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix
open ActualEisensteinCubic ConcreteTraceCRT CubicKubota
local notation "O" => ActualEisensteinCubic.O
attribute [fun_prop] hyperbolicGram_continuous hyperbolicFrobenius_continuous

theorem OAI.CubicEisenstein.hyperbolicFundamentalSet_orbit_unique (H : Subgroup (SL(2,O))) (w : HyperbolicSpace)
    (hw : w∈hyperbolicFundamentalSet H) (M : H)
    (hMw : M • w∈hyperbolicFundamentalSet H) : M • w=w := by sorry
