-- Prove2me | Theorems.Thm_GlobalTheory_mem_span_iff_finrank_option_eq
-- name    : GlobalTheory.mem_span_iff_finrank_option_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T02:55:24.070173+00:00
-- url     : https://prove2.me/theorems/da53c807-835a-4d76-b1c9-fb0c73bf105a
-- title:
--   Global Theory: mem span iff finrank option eq
-- statement:
--   The Global Theory construction uses the mem span iff finrank option eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/LinearIndependentRingHomCompIff.lean#L38-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/LinearIndependentRingHomCompIff.lean#L38-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LinearIndependentRingHomCompIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.mem_span_iff_finrank_option_eq {F V ι : Type} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (v : Option ι → V) :
    v none ∈ Submodule.span F (Set.range fun i => v (some i)) ↔
      Module.finrank F (Submodule.span F (Set.range fun i => v (some i))) =
        Module.finrank F (Submodule.span F (Set.range v)) := by sorry
