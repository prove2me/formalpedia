-- Prove2me | Theorems.Thm_GlobalTheory_Klein_not_red_addSubgroup
-- name    : GlobalTheory.Klein.not_red_addSubgroup
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:17:08.979831+00:00
-- url     : https://prove2.me/theorems/587d07e5-73cf-45b1-8799-535b7f4c896a
-- title:
--   Klein: not red add Subgroup
-- statement:
--   The Klein construction uses the not red add Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ReductionSetSubgroup.lean#L123-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ReductionSetSubgroup.lean#L123-L132

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

theorem GlobalTheory.Klein.not_red_addSubgroup : ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (L : PeriodPair) (r : ℂ), Good ι L r → (∀ z, Red ι L r z → Red ι L r (-z)) ∧ (∀ z, Red ι L r z → ∀ ω ∈ L.lattice, Red ι L r (z + ω)) ∧ (∀ u w, ¬ Red ι L r u → Red ι L r w → Red ι L r (u + w)) ∧ ∃ G : AddSubgroup ℂ, (∀ z, z ∈ G ↔ ¬ Red ι L r z) ∧ ∀ ω ∈ L.lattice, ω ∈ G := by sorry
