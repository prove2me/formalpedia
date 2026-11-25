-- Prove2me | Theorems.Thm_GlobalTheory_HL_FrameTuple_tup_change
-- name    : GlobalTheory.HL.FrameTuple.tup_change
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:34:56.282492+00:00
-- url     : https://prove2.me/theorems/fefcdf0c-95c5-5b99-a82f-83b6e4006e19
-- title:
--   Frame Tuple: tup change
-- statement:
--   The Frame Tuple construction uses the tup change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsNondegenerateTupleComplementFixer.lean#L55-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsNondegenerateTupleComplementFixer.lean#L55-L64

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsNondegenerateTupleComplementFixer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameTuple
variable {E V : Type} [CommRing E] [AddCommGroup V] [Module E V] {m : ℕ}

theorem GlobalTheory.HL.FrameTuple.tup_change (t : E) (g g' p p' : Fin m → V) (u u' : Matrix (Fin m) (Fin m) E)
    (hp : ∀ j, p j = ∑ i, u i j • g i) (hp' : ∀ j, p' j = ∑ i, u' i j • g' i) (j) :
    tup t p p' j = ∑ i, (Matrix.fromBlocks u (t • (u' - u)) 0 u') i j • tup t g g' i := by sorry
