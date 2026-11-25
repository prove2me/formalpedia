-- Prove2me | Theorems.Thm_GlobalTheory_exists_integer_add_star_eq_one_of_isCMUnram
-- name    : GlobalTheory.exists_integer_add_star_eq_one_of_isCMUnram
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:33:31.136807+00:00
-- url     : https://prove2.me/theorems/fe70e149-df2e-4611-8c60-506256542e07
-- title:
--   Global Theory: exists integer add star eq one of is CMUnram
-- statement:
--   The Global Theory construction uses the exists integer add star eq one of is CMUnram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsIntegerAddStarEqOneOfIsCMUnram.lean#L21-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsIntegerAddStarEqOneOfIsCMUnram.lean#L21-L64

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntegerAddStarEqOneOfIsCMUnram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal
open GlobalTheory
open NumberField Module Matrix
open scoped ENNReal

theorem GlobalTheory.exists_integer_add_star_eq_one_of_isCMUnram :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K], _root_.Formalism.HermitianLatticesTheory.IsCMUnram K →
      ∃ t : 𝓞 K, (t : K) + star (t : K) = 1 := by sorry
