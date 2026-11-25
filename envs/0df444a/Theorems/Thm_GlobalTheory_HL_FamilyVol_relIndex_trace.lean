-- Prove2me | Theorems.Thm_GlobalTheory_HL_FamilyVol_relIndex_trace
-- name    : GlobalTheory.HL.FamilyVol.relIndex_trace
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:30:03.450144+00:00
-- url     : https://prove2.me/theorems/a1352667-e517-5aba-aab6-ab32e8299e88
-- title:
--   Family Vol: rel Index trace
-- statement:
--   The Family Vol construction uses the rel Index trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFamilyTraceVolumeConst.lean#L73-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFamilyTraceVolumeConst.lean#L73-L96

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SelfDualHermitianLatticeTraceOrthogonalVolumeRatStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameLatticeTraceInitialSpanVolumeEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFamilyTraceVolumeConst
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FamilyVol
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : LocE F E} {r k : ℕ}

theorem GlobalTheory.HL.FamilyVol.relIndex_trace (S : Frames L r k) (J : ℕ) (hJ : J ≤ r + 1) (d : S.Datum) (Λ : Submodule L.O S.V)
    (hT : S.IsTerm d Λ) (hl : ∀ y ∈ S.sat Λ, S.levC d Λ y ≤ J) :
    (S.M d Λ ⊓ (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O).toAddSubgroup.relIndex
      (Λ ⊓ (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O).toAddSubgroup = S.be d Λ := by sorry
