-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_CompletedAlgClosure_norm_embedding
-- name    : GroundTheory.PAdicHodge.CompletedAlgClosure.norm_embedding
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:45:52.764662+00:00
-- url     : https://prove2.me/theorems/db5a6135-3ec0-45a5-b24b-5227e8fa42d5
-- title:
--   Completed Alg Closure: norm embedding
-- statement:
--   The Completed Alg Closure construction uses the norm embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CompletedAlgClosure.lean#L58-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CompletedAlgClosure.lean#L58-L68

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_CompletedAlgClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
variable (K : Type*) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
open GroundTheory.PAdicHodge.CompletedAlgClosure
variable (L : Type*) [NormedField L] [NormedAlgebra K L] [Algebra.IsAlgebraic K L]

theorem GroundTheory.PAdicHodge.CompletedAlgClosure.norm_embedding (x : L) : ‖embedding K L x‖ = ‖x‖ := by sorry
