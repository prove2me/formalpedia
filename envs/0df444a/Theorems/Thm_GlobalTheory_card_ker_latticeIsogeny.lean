-- Prove2me | Theorems.Thm_GlobalTheory_card_ker_latticeIsogeny
-- name    : GlobalTheory.card_ker_latticeIsogeny
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:07:23.554681+00:00
-- url     : https://prove2.me/theorems/23d88c4f-a9eb-48b2-87a3-aa29deb81064
-- title:
--   Global Theory: card ker lattice Isogeny
-- statement:
--   The Global Theory construction uses the card ker lattice Isogeny property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/AddMonoidHomEqZeroOfEventually.lean#L28-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/AddMonoidHomEqZeroOfEventually.lean#L28-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNumeratorOfInvolution
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsMulEqPolynomialWeierstrassP
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddMonoidHomEqZeroOfEventually
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter PeriodPair Polynomial WeierstrassCurve UpperHalfPlane
open scoped Topology
noncomputable section
open GlobalTheory
variable {L L' : PeriodPair} {α : ℂ}

theorem GlobalTheory.card_ker_latticeIsogeny (hα0 : α ≠ 0) (hα : ∀ l ∈ L.lattice, α * l ∈ L'.lattice) :
    Nat.card (latticeIsogeny α hα).ker =
      (L.lattice.toAddSubgroup.map (AddMonoidHom.mulLeft α)).relIndex
        L'.lattice.toAddSubgroup := by sorry
