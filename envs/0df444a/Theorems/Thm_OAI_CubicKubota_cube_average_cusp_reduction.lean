-- Prove2me | Theorems.Thm_OAI_CubicKubota_cube_average_cusp_reduction
-- name    : OAI.CubicKubota.cube_average_cusp_reduction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:31:04.383197+00:00
-- url     : https://prove2.me/theorems/62d0cf92-a193-401d-97cd-f8cc9d15264d
-- title:
--   Cubic Kubota: cube average cusp reduction
-- statement:
--   The Cubic Kubota construction uses the cube average cusp reduction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/CuspDilation.lean#L589-L633
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/CuspDilation.lean#L589-L633

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ArbitraryCuspPullback
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CuspDilation
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
open scoped BigOperators Classical
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open scoped Classical MatrixGroups
open OAI.CubicKubota
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

theorem OAI.CubicKubota.cube_average_cusp_reduction (A : SL(2,Eis)) (p q : Eis)
    (hp : Prime p) (hprimary : lambda^2∣p-1) :
    ∃ j≤3,∃N : SL(2,Eis),
      A 0 0+3*q*A 1 0=p^j*N 0 0 ∧
      p^3*A 1 0=p^j*N 1 0 ∧ N*A⁻¹∈levelThree ∧
      (j=3 ∨ ¬p∣N 0 0) ∧
      N.val⁻¹*(!![1,3*q;0,p^3]*A.val)=
        !![p^j,(N.val⁻¹*(!![1,3*q;0,p^3]*A.val)) 0 1;0,p^(3-j)] := by sorry
