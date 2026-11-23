-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_extendToClosure_of_mem
-- name    : GroundTheory.PAdicHodge.extendToClosure_of_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:24:51.968778+00:00
-- url     : https://prove2.me/theorems/7da45493-59a3-4f94-8f01-eeb98fc4c005
-- title:
--   PAdic Hodge: extend To Closure of mem
-- statement:
--   The PAdic Hodge construction uses the extend To Closure of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceClosure.lean#L62-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceClosure.lean#L62-L64

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceClosure
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
open UniformSpace Topology Filter Set
noncomputable section
variable {p : ℕ} [Fact p.Prime]
variable (E : IntermediateField ℚ_[p] (PadicAlgCl p))
variable (R : PadicAlgCl p → PadicAlgCl p)
variable {E R}

theorem GroundTheory.PAdicHodge.extendToClosure_of_mem {x : ℂ_[p]} (hx : x ∈ closureInCp E) :
    extendToClosure E R x = extendOnClosure E R ⟨x, hx⟩ := by sorry
