-- Prove2me | Theorems.Thm_GlobalTheory_HL_CoordSum_tsum_reps_eq
-- name    : GlobalTheory.HL.CoordSum.tsum_reps_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:44:44.126596+00:00
-- url     : https://prove2.me/theorems/326657a7-a536-5a09-addd-d08764aff901
-- title:
--   Coord Sum: tsum reps eq
-- statement:
--   The Coord Sum construction uses the tsum reps eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFramePairTsumRepsEqConstMulOrbits.lean#L18-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFramePairTsumRepsEqConstMulOrbits.lean#L18-L81

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesComplementUnitaryActsOnTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InfStabilizerSmulEqConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TsumTransversalEqTsumOrbitQuotientGeneral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramePairCoordinatesTransportInnerData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermsCorrespondStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsWtEqMulNuStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramePairTsumRepsEqConstMulOrbits
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CoordSum

theorem GlobalTheory.HL.CoordSum.tsum_reps_eq : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), ∀ (R : LocNG.Reps P) (d0 : LocNG.Datum P), ∃ κ : ℝ, 0 ≤ κ ∧ ∀ φ : S.Datum → ℝ≥0∞, (∀ h ∈ S.H0, ∀ δ, φ (h • δ) = φ δ) → (∀ δ, (¬ ∃ Λ, S.IsTerm δ Λ) → φ δ = 0) → (∑' d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) * φ (c.dat d.1)) = ENNReal.ofReal κ * S.sumData φ := by sorry
