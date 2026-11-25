-- Prove2me | Theorems.Thm_GlobalTheory_HL_BlockStab_cj_mem_iff
-- name    : GlobalTheory.HL.BlockStab.cj_mem_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:59:07.387851+00:00
-- url     : https://prove2.me/theorems/e4231293-293e-4103-8ab9-45e6ff32948d
-- title:
--   Block Stab: cj mem iff
-- statement:
--   The Block Stab construction uses the cj mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFramesPairingStabilizerBlockDiagonal.lean#L116-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFramesPairingStabilizerBlockDiagonal.lean#L116-L120

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
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {n : ℕ}

theorem GlobalTheory.HL.BlockStab.cj_mem_iff (L : LocE F E) {x : E} : L.cj x ∈ L.O ↔ x ∈ L.O := by sorry
