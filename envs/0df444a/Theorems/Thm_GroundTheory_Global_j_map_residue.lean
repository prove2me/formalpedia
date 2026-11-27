-- Prove2me | Theorems.Thm_GroundTheory_Global_j_map_residue
-- name    : GroundTheory.Global.j_map_residue
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:56:16.510349+00:00
-- url     : https://prove2.me/theorems/b19879ed-f0e7-53ce-9a58-f32a01a71c9f
-- title:
--   Global: j map residue
-- statement:
--   The Global construction uses the j map residue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/GoodReductionAlmostAll.lean#L61-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/GoodReductionAlmostAll.lean#L61-L63

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_PrimeLocalization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_GoodReductionAlmostAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain IsLocalRing
noncomputable section
variable {L : Type*} [Field L] [NumberField L]

theorem GroundTheory.Global.j_map_residue {R : Type*} [CommRing R] [IsLocalRing R] (W : WeierstrassCurve R)
    [W.IsElliptic] : (W.map (residue R)).j = residue R W.j := by sorry
