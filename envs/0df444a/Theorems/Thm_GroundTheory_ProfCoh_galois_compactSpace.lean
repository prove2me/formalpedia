-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_galois_compactSpace
-- name    : GroundTheory.ProfCoh.galois_compactSpace
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:02:12.693718+00:00
-- url     : https://prove2.me/theorems/52398384-4c03-486c-a6b2-55e3d952df60
-- title:
--   Prof Coh: galois compact Space
-- statement:
--   The Prof Coh construction uses the galois compact Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GaloisModules/Discrete.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GaloisModules/Discrete.lean#L17-L18

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_DiscreteModules
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_CoeGalRootsOfUnityHomApply
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_Discrete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.ProfCoh
open IntermediateField
universe w u
variable {K : Type*} {L : Type u} [Field K] [Field L] [Algebra K L]
variable (K L)

theorem GroundTheory.ProfCoh.galois_compactSpace [IsGalois K L] : CompactSpace Gal(L/K) := by sorry
