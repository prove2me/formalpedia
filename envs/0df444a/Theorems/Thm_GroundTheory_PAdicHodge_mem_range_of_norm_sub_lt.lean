-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_mem_range_of_norm_sub_lt
-- name    : GroundTheory.PAdicHodge.mem_range_of_norm_sub_lt
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:46:53.944617+00:00
-- url     : https://prove2.me/theorems/e90d4459-ec26-4d91-9bf2-5d95e2750576
-- title:
--   PAdic Hodge: mem range of norm sub lt
-- statement:
--   The PAdic Hodge construction uses the mem range of norm sub lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltApproxLemmas.lean#L29-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltApproxLemmas.lean#L29-L51

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Definitions.Def_GroundTheory_PAdicHodge_UntiltApproxLemmas
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
open Polynomial
variable {F E : Type*} [NontriviallyNormedField F] [CompleteSpace F] [IsUltrametricDist F]
  [NormedField E] [NormedAlgebra F E]

theorem GroundTheory.PAdicHodge.mem_range_of_norm_sub_lt [IsAlgClosed E] {α : E} (b : F) (hα : IsSeparable F α)
    (h : ∀ α' : E, IsConjRoot F α α' → α ≠ α' → ‖α - algebraMap F E b‖ < ‖α - α'‖) :
    α ∈ Set.range (algebraMap F E) := by sorry
