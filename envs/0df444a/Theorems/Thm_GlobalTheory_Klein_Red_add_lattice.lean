-- Prove2me | Theorems.Thm_GlobalTheory_Klein_Red_add_lattice
-- name    : GlobalTheory.Klein.Red.add_lattice
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:03:15.05445+00:00
-- url     : https://prove2.me/theorems/df64f5e8-7233-4328-804e-8156d29aa4fc
-- title:
--   Red: add lattice
-- statement:
--   The Red construction uses the add lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ReductionSetSubgroup.lean#L86-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ReductionSetSubgroup.lean#L86-L90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_NotRedOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ReductionSetSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.Th1.F GlobalTheory.Klein
open scoped ComplexConjugate BigOperators
open GlobalTheory GlobalTheory.Klein
variable {p : ℕ} [Fact p.Prime]

theorem GlobalTheory.Klein.Red.add_lattice {ι : ℂ ≃+* ℂ_[p]} {L : PeriodPair} {r z ω : ℂ} (h : Red ι L r z)
    (hω : ω ∈ L.lattice) : Red ι L r (z + ω) := by sorry
