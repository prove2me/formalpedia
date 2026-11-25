-- Prove2me | Theorems.Thm_GlobalTheory_etale_of_grpObj_of_isFinite
-- name    : GlobalTheory.etale_of_grpObj_of_isFinite
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:44:53.023501+00:00
-- url     : https://prove2.me/theorems/5b5b99ab-e712-5dc6-be08-a985f0fb2748
-- title:
--   Global Theory: etale of grp Obj of is Finite
-- statement:
--   The Global Theory construction uses the etale of grp Obj of is Finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsCounitEqOneMulEqZeroOfIsNilpotent.lean#L307-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsCounitEqOneMulEqZeroOfIsNilpotent.lean#L307-L318

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsCounitDerivationCounitComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsCounitEqOneMulEqZeroOfIsNilpotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Coalgebra Bialgebra HopfAlgebra WithConv
open scoped TensorProduct
open GlobalTheory
open CategoryTheory AlgebraicGeometry
universe u
variable {k : Type u} [Field k] [CharZero k] {G : Scheme.{u}} (f : G ⟶ Spec (.of k))
  [GrpObj (Over.mk f)]

theorem GlobalTheory.etale_of_grpObj_of_isFinite [IsFinite f] : Etale f := by sorry
