-- Prove2me | Theorems.Thm_GlobalTheory_HL_BlockStab_stabiliser_blockDiag
-- name    : GlobalTheory.HL.BlockStab.stabiliser_blockDiag
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:14:27.659684+00:00
-- url     : https://prove2.me/theorems/851179af-cbed-53a6-abe7-279ac5398591
-- title:
--   Block Stab: stabiliser block Diag
-- statement:
--   The Block Stab construction uses the stabiliser block Diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFramesPairingStabilizerBlockDiagonal.lean#L206-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFramesPairingStabilizerBlockDiagonal.lean#L206-L230

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesPairingStabilizerBlockDiagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.BlockStab

theorem GlobalTheory.HL.BlockStab.stabiliser_blockDiag : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (∀ s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUni s → IsUni s' → cT L s * S.Zh * s' = S.Zh → (∀ i j : Fin (r + 1), sameBlock S.w.blocks i j = false → s i j = 0 ∧ s' i j = 0) ∧ (IsIntM L s ↔ IsIntM L s')) ∧ ∀ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUni s → (∀ i j : Fin (r + 1), sameBlock S.w.blocks i j = false → s i j = 0) → ∃ s', IsUni s' ∧ cT L s * S.Zh * s' = S.Zh := by sorry
