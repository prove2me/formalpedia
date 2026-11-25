-- Prove2me | Theorems.Thm_GlobalTheory_HL_RStab_rmul_sub
-- name    : GlobalTheory.HL.RStab.rmul_sub
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:53:39.121404+00:00
-- url     : https://prove2.me/theorems/f3daeee9-8eac-5283-860d-2053f0cc1636
-- title:
--   RStab: rmul sub
-- statement:
--   The RStab construction uses the rmul sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsIsometryTupleMatrixRightMulNearIdentity.lean#L24-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsIsometryTupleMatrixRightMulNearIdentity.lean#L24-L29

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NcardImageOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryNearIdentityCloseTuplesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryTupleMatrixRightMulNearIdentity
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.RStab

theorem GlobalTheory.HL.RStab.rmul_sub {E : Type} [CommRing E] {n m : ℕ} (x : Fin m → Fin n → E)
    (A : Matrix (Fin m) (Fin m) E) (a : Fin m) :
    rmul x A a - x a = ∑ i, (A i a - (1 : Matrix (Fin m) (Fin m) E) i a) • x i := by sorry
