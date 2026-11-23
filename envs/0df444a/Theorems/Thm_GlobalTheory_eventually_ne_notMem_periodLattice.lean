-- Prove2me | Theorems.Thm_GlobalTheory_eventually_ne_notMem_periodLattice
-- name    : GlobalTheory.eventually_ne_notMem_periodLattice
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:04.863294+00:00
-- url     : https://prove2.me/theorems/0b2e014a-d135-4153-922c-feaca1ad4f91
-- title:
--   Global Theory: eventually ne not Mem period Lattice
-- statement:
--   The Global Theory construction uses the eventually ne not Mem period Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/WeierstrassPAddOfNeOfDerivNeZero.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/WeierstrassPAddOfNeOfDerivNeZero.lean#L25-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter PeriodPair Bornology
open scoped Topology
noncomputable section
open GlobalTheory
variable (L : PeriodPair)

theorem GlobalTheory.eventually_ne_notMem_periodLattice (z : ℂ) : ∀ᶠ w in 𝓝[≠] z, w ∉ L.lattice := by sorry
