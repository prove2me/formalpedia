-- Prove2me | Theorems.Thm_GlobalTheory_OrbitAvg_stab_finiteIndex
-- name    : GlobalTheory.OrbitAvg.stab_finiteIndex
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:37:34.186575+00:00
-- url     : https://prove2.me/theorems/fecb9583-c461-419d-8a2a-37a7be03fb5d
-- title:
--   Orbit Avg: stab finite Index
-- statement:
--   The Orbit Avg construction uses the stab finite Index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAveragingProjection.lean#L79-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAveragingProjection.lean#L79-L98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAveragingProjection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.OrbitAvg
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
  (π : G →* Module.End ℂ V) (L : Subgroup G)

theorem GlobalTheory.OrbitAvg.stab_finiteIndex {x : V} (hx : (Set.range fun l : L => π (l : G) x).Finite) :
    (stab π L x).FiniteIndex := by sorry
