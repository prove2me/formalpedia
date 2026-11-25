-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_map_fst_map_conjHom_prod
-- name    : GroundTheory.Automorphic.map_fst_map_conjHom_prod
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:53:45.541903+00:00
-- url     : https://prove2.me/theorems/b2c1ae88-dbff-520c-bae1-3213eb2d256d
-- title:
--   Automorphic: map fst map conj Hom prod
-- statement:
--   The Automorphic construction uses the map fst map conj Hom prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianSplit.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianSplit.lean#L12-L16

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

theorem GroundTheory.Automorphic.map_fst_map_conjHom_prod {ι : Type*} (M : Matrix ι ι (F × F)) :
    (M.map (conjHom F (F × F))).map (RingHom.fst F F) = M.map (RingHom.snd F F) := by sorry
