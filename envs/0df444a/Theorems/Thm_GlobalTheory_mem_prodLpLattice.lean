-- Prove2me | Theorems.Thm_GlobalTheory_mem_prodLpLattice
-- name    : GlobalTheory.mem_prodLpLattice
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:21.697493+00:00
-- url     : https://prove2.me/theorems/6b42901d-be08-4b29-be9f-edfefd42d972
-- title:
--   Global Theory: mem prod Lp Lattice
-- statement:
--   The Global Theory construction uses the mem prod Lp Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsAddFundamentalDomainLatticeDomain.lean#L293-L294
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsAddFundamentalDomainLatticeDomain.lean#L293-L294

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsAddFundamentalDomainLatticeDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Submodule Set
open GlobalTheory
noncomputable section
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] (L : Submodule ℤ E) (L' : Submodule ℤ E')

theorem GlobalTheory.mem_prodLpLattice {x : WithLp 2 (E × E')} :
    x ∈ prodLpLattice L L' ↔ x.fst ∈ L ∧ x.snd ∈ L' := by sorry
