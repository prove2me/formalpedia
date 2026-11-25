-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_galois_isProfinite
-- name    : GroundTheory.ProfCoh.galois_isProfinite
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:51:30.940065+00:00
-- url     : https://prove2.me/theorems/5312f603-4d82-4c7d-bcd5-4dddfc1438a0
-- title:
--   Prof Coh: galois is Profinite
-- statement:
--   The Prof Coh construction uses the galois is Profinite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GaloisModules/Discrete.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GaloisModules/Discrete.lean#L23-L25

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

theorem GroundTheory.ProfCoh.galois_isProfinite [IsGalois K L] :
    CompactSpace Gal(L/K) ∧ T2Space Gal(L/K) ∧ TotallyDisconnectedSpace Gal(L/K) := by sorry
