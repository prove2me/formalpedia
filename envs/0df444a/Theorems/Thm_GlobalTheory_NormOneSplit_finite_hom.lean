-- Prove2me | Theorems.Thm_GlobalTheory_NormOneSplit_finite_hom
-- name    : GlobalTheory.NormOneSplit.finite_hom
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:32:20.566674+00:00
-- url     : https://prove2.me/theorems/410b5f70-69d6-58ac-91fb-80bc1e7f1f51
-- title:
--   Norm One Split: finite hom
-- statement:
--   The Norm One Split construction uses the finite hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsForallHomEq.lean#L68-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsForallHomEq.lean#L68-L78

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsForallHomEq
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
open GlobalTheory GlobalTheory.NormOneSplit
open NumberField Module Matrix
open scoped ENNReal

theorem GlobalTheory.NormOneSplit.finite_hom {E : Type} [Field E] [NumberField E] {T : ℕ}
    (hT : T.Prime) :
    Finite (𝓞 E →+* ZMod T) := by sorry
