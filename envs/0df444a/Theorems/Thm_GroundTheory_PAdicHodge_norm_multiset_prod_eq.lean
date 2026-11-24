-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_multiset_prod_eq
-- name    : GroundTheory.PAdicHodge.norm_multiset_prod_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:29:11.370487+00:00
-- url     : https://prove2.me/theorems/365209dd-5128-4cb3-b8b4-e48b4da4c19d
-- title:
--   PAdic Hodge: norm multiset prod eq
-- statement:
--   The PAdic Hodge construction uses the norm multiset prod eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L117-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L117-L120

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
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
open Polynomial
noncomputable section
variable {E : Type*} [NormedField E] [IsUltrametricDist E]
omit [IsUltrametricDist E]

theorem GroundTheory.PAdicHodge.norm_multiset_prod_eq (s : Multiset E) : ‖s.prod‖ = (s.map norm).prod := by sorry
