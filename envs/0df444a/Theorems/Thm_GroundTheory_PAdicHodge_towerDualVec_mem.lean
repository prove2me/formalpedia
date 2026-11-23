-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_towerDualVec_mem
-- name    : GroundTheory.PAdicHodge.towerDualVec_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:30.692516+00:00
-- url     : https://prove2.me/theorems/7e4f06e1-d27c-406d-b4ad-4f92393277fc
-- title:
--   PAdic Hodge: tower Dual Vec mem
-- statement:
--   The PAdic Hodge construction uses the tower Dual Vec mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceTower.lean#L133-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceTower.lean#L133-L135

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceTower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial Module
noncomputable section
variable {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
variable [FiniteDimensional ℚ_[p] K]

theorem GroundTheory.PAdicHodge.towerDualVec_mem (i : Fin (relDeg K (stableIndex K))) :
    towerDualVec K i ∈ cyclotomicLayer K (stableIndex K) := by sorry
