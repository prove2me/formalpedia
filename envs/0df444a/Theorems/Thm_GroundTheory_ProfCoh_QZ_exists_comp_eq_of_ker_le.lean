-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_QZ_exists_comp_eq_of_ker_le
-- name    : GroundTheory.ProfCoh.QZ.exists_comp_eq_of_ker_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:33:41.915961+00:00
-- url     : https://prove2.me/theorems/d4dc407d-b1f5-574b-91da-4cc09867fcd2
-- title:
--   QZ: exists comp eq of ker le
-- statement:
--   The QZ construction uses the exists comp eq of ker le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/TorsionDualFinite.lean#L74-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/TorsionDualFinite.lean#L74-L87

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_TorsionDualDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_TorsionDualFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open Function
open GroundTheory.ProfCoh.QZ
variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

theorem GroundTheory.ProfCoh.QZ.exists_comp_eq_of_ker_le (h : G →+ H) (χ : G →+ QZ) (hχ : h.ker ≤ χ.ker) :
    ∃ ψ : H →+ QZ, ψ.comp h = χ := by sorry
