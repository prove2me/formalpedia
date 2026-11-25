-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_QZ_exists_comp_eq_of_injective
-- name    : GroundTheory.ProfCoh.QZ.exists_comp_eq_of_injective
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:34:20.289773+00:00
-- url     : https://prove2.me/theorems/89f0021d-d9c7-4918-a070-c796a1a7f15f
-- title:
--   QZ: exists comp eq of injective
-- statement:
--   The QZ construction uses the exists comp eq of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/TorsionDualFinite.lean#L65-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/TorsionDualFinite.lean#L65-L72

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

theorem GroundTheory.ProfCoh.QZ.exists_comp_eq_of_injective (i : G →+ H) (hi : Injective i) (f : G →+ QZ) :
    ∃ g : H →+ QZ, g.comp i = f := by sorry
