-- Prove2me | Theorems.Thm_GlobalTheory_HL_VolPerp_relIndex_split
-- name    : GlobalTheory.HL.VolPerp.relIndex_split
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:34:46.625396+00:00
-- url     : https://prove2.me/theorems/757dd569-fbb7-4770-9b93-69b26a573e60
-- title:
--   Vol Perp: rel Index split
-- statement:
--   The Vol Perp construction uses the rel Index split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SelfDualHermitianLatticeTraceOrthogonalVolumeRat.lean#L14-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SelfDualHermitianLatticeTraceOrthogonalVolumeRat.lean#L14-L23

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DualInterSelfDualHermitianLatticeSubspace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexSpanLatticeMatrixDetNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SelfDualHermitianLatticeTraceOrthogonalVolumeRat
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.VolPerp
open GlobalTheory.HL.DualInter

theorem GlobalTheory.HL.VolPerp.relIndex_split {G : Type} [AddCommGroup G] {M A : AddSubgroup G} (Z : AddSubgroup G)
    (h : M ≤ A) : M.relIndex A = (M ⊓ Z).relIndex (A ⊓ Z) * (M ⊔ Z).relIndex (A ⊔ Z) := by sorry
