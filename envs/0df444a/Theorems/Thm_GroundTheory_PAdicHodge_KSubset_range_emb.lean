-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_KSubset_range_emb
-- name    : GroundTheory.PAdicHodge.KSubset.range_emb
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:46:13.670878+00:00
-- url     : https://prove2.me/theorems/19bb5a2d-d25b-4ceb-818b-9b9b2d54840f
-- title:
--   KSubset: range emb
-- statement:
--   The KSubset construction uses the range emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SlopeCauchyBinet.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SlopeCauchyBinet.lean#L13-L14

import Mathlib
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_ExistsMaxMinorNeZeroOfLinearIndependentAlt
import Definitions.Def_GroundTheory_PAdicHodge_SlopeCauchyBinet
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
open Matrix Finset Equiv

theorem GroundTheory.PAdicHodge.KSubset.range_emb {n k : ℕ} (s : KSubset n k) : Set.range s.emb = (s.1 : Set (Fin n)) := by sorry
