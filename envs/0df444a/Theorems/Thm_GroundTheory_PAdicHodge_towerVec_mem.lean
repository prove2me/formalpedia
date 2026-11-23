-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_towerVec_mem
-- name    : GroundTheory.PAdicHodge.towerVec_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:51.360254+00:00
-- url     : https://prove2.me/theorems/4a31d912-2ac2-4a39-a5d0-7d1c457d8bbf
-- title:
--   PAdic Hodge: tower Vec mem
-- statement:
--   The PAdic Hodge construction uses the tower Vec mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceTower.lean#L129-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceTower.lean#L129-L131

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

theorem GroundTheory.PAdicHodge.towerVec_mem (i : Fin (relDeg K (stableIndex K))) :
    towerVec K i ∈ cyclotomicLayer K (stableIndex K) := by sorry
