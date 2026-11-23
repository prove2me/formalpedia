-- Prove2me | Theorems.Thm_GlobalTheory_isIntegrallyClosed_sections_of_stalks
-- name    : GlobalTheory.isIntegrallyClosed_sections_of_stalks
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:26.734129+00:00
-- url     : https://prove2.me/theorems/9f22a30d-1953-4cb5-8239-dae98cdabd1c
-- title:
--   Global Theory: is Integrally Closed sections of stalks
-- statement:
--   The Global Theory construction uses the is Integrally Closed sections of stalks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/BijectiveAlgebraMapIntegralClosureOfBirational.lean#L16-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/BijectiveAlgebraMapIntegralClosureOfBirational.lean#L16-L29

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

theorem GlobalTheory.isIntegrallyClosed_sections_of_stalks [IsIntegral Y]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) {U : Y.Opens} (hU : IsAffineOpen U)
    [Nonempty U] : IsIntegrallyClosed Γ(Y, U) := by sorry
