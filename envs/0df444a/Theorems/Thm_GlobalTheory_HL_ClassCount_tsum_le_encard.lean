-- Prove2me | Theorems.Thm_GlobalTheory_HL_ClassCount_tsum_le_encard
-- name    : GlobalTheory.HL.ClassCount.tsum_le_encard
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:32:14.678246+00:00
-- url     : https://prove2.me/theorems/0f14c528-4a48-56d2-ba55-b41415eb011c
-- title:
--   Class Count: tsum le encard
-- statement:
--   The Class Count construction uses the tsum le encard property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SumClsLeEncard.lean#L19-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SumClsLeEncard.lean#L19-L49

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MassOrbitsEqTsumFiber
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliserStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFrameClassPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommonStabilizerStabilizersCommensurableVolumeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesPairingStabilizerBlockDiagonalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeStabilizerInfLeConjNormalisingSubgroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SumClsLeEncard
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.ClassCount

theorem GlobalTheory.HL.ClassCount.tsum_le_encard {G X : Type*} [Group G] [MulAction G X] (H K0 : Subgroup G) (hK : K0 ≤ H)
    (P Q : X → Prop) (w : X → ℝ)
    (hP : ∀ x, P x → ∃ h ∈ H, w x = invVol K0 (H ⊓ MulAction.stabilizer G (h • x)) ∧
      H ⊓ MulAction.stabilizer G (h • x) ≤ K0 ∧ ∀ k ∈ K0, Q (k • h • x)) :
    (∑' o : MulAction.orbitRel.Quotient H X, if P o.out then ENNReal.ofReal (w o.out) * 1 else 0)
      ≤ (({x | Q x} : Set X).encard : ℝ≥0∞) := by sorry
