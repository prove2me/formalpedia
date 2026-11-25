-- Prove2me | Theorems.Thm_GlobalTheory_HL_LocComm_stab_commensurable
-- name    : GlobalTheory.HL.LocComm.stab_commensurable
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:53:41.030798+00:00
-- url     : https://prove2.me/theorems/d5ef41dc-3309-545b-8eea-939ffd919c60
-- title:
--   Loc Comm: stab commensurable
-- statement:
--   The Loc Comm construction uses the stab commensurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianTermStabilizerCommensurable.lean#L18-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianTermStabilizerCommensurable.lean#L18-L70

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NotField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramePairCoordinatesTransportUnitaryMassStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramePairCoordinatesTransportInnerDataStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermsCorrespondStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StabilizerCommensurableInvVolumeSmulComplementStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesComplementUnitaryActsOnTermsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianTermStabilizerCommensurable
import Theorems.Thm_GlobalTheory_LatComm_stab_commensurable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.LocComm

theorem GlobalTheory.HL.LocComm.stab_commensurable : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (d : LocNG.Datum P) (τ : Term V M r), LocNG.IsTermOver P d τ → P.UW0 ⊓ LocNG.Aut τ.abelian₂ ≤ LocNG.Datum.Stab d ∧ (P.UW0 ⊓ LocNG.Aut τ.abelian₂).relIndex (LocNG.Datum.Stab d) ≠ 0 ∧ ∀ (d' : LocNG.Datum P) (τ' : Term V M r), LocNG.IsTermOver P d' τ' → (LocNG.Datum.Stab d).relIndex (LocNG.Datum.Stab d') ≠ 0 := by sorry
