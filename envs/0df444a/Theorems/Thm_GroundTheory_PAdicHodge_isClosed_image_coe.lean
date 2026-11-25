-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_isClosed_image_coe
-- name    : GroundTheory.PAdicHodge.isClosed_image_coe
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:47:03.543801+00:00
-- url     : https://prove2.me/theorems/42dec312-12d6-4bc8-b728-a40c257f6cd4
-- title:
--   PAdic Hodge: is Closed image coe
-- statement:
--   The PAdic Hodge construction uses the is Closed image coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceClosure.lean#L66-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceClosure.lean#L66-L74

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

theorem GroundTheory.PAdicHodge.isClosed_image_coe (k : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] k] :
    IsClosed (((↑) : PadicAlgCl p → ℂ_[p]) '' (k : Set (PadicAlgCl p))) := by sorry
