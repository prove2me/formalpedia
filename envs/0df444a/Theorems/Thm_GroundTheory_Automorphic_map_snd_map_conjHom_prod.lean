-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_map_snd_map_conjHom_prod
-- name    : GroundTheory.Automorphic.map_snd_map_conjHom_prod
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:54:36.672684+00:00
-- url     : https://prove2.me/theorems/06b29c0f-3a15-4c34-9513-06ba29766cb0
-- title:
--   Automorphic: map snd map conj Hom prod
-- statement:
--   The Automorphic construction uses the map snd map conj Hom prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianSplit.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianSplit.lean#L18-L22

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitarySplit
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSpaces
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Module Matrix
variable {F : Type*} [Field F]
variable {V V' : Type*} [AddCommGroup V] [Module (F × F) V] [AddCommGroup V'] [Module (F × F) V']

theorem GroundTheory.Automorphic.map_snd_map_conjHom_prod {ι : Type*} (M : Matrix ι ι (F × F)) :
    (M.map (conjHom F (F × F))).map (RingHom.snd F F) = M.map (RingHom.fst F F) := by sorry
