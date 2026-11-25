-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_QZ_evalHom_apply
-- name    : GroundTheory.ProfCoh.QZ.evalHom_apply
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:17:05.167982+00:00
-- url     : https://prove2.me/theorems/431dd0e6-78b3-524a-bc57-6173244cee14
-- title:
--   QZ: eval Hom apply
-- statement:
--   The QZ construction uses the eval Hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/TorsionDualFinite.lean#L105-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/TorsionDualFinite.lean#L105-L106

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

theorem GroundTheory.ProfCoh.QZ.evalHom_apply (a : G) (f : G →+ QZ) : evalHom G a f = f a := by sorry

attribute [defeq] GroundTheory.ProfCoh.QZ.evalHom_apply
