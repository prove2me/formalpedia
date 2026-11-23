-- Prove2me | Theorems.Thm_GlobalTheory_isFractionRing_stalk_of_eq_genericPoint
-- name    : GlobalTheory.isFractionRing_stalk_of_eq_genericPoint
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:33.739803+00:00
-- url     : https://prove2.me/theorems/c22809c7-f9a3-4336-989d-178782267c2b
-- title:
--   Global Theory: is Fraction Ring stalk of eq generic Point
-- statement:
--   The Global Theory construction uses the is Fraction Ring stalk of eq generic Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/BijectiveAlgebraMapIntegralClosureOfBirational.lean#L43-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/BijectiveAlgebraMapIntegralClosureOfBirational.lean#L43-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology
open GlobalTheory
universe u
variable {X Y : Scheme.{u}}
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology
variable {X Y : Scheme.{u}}

theorem GlobalTheory.isFractionRing_stalk_of_eq_genericPoint [IsIntegral Y] {U : Y.Opens} (hU : IsAffineOpen U)
    (y : Y) (hyU : y ∈ U) (hy : y = genericPoint Y) :
    letI := Y.presheaf.algebra_section_stalk (U := U) ⟨y, hyU⟩
    IsFractionRing Γ(Y, U) (Y.presheaf.stalk y) := by sorry
