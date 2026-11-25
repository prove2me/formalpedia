-- Prove2me | Theorems.Thm_GlobalTheory_HL_DatumStab_mem_smul_iff
-- name    : GlobalTheory.HL.DatumStab.mem_smul_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:14:37.131707+00:00
-- url     : https://prove2.me/theorems/2ba24919-4301-4705-aac5-fed9caa24a13
-- title:
--   Datum Stab: mem smul iff
-- statement:
--   The Datum Stab construction uses the mem smul iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DatumStabilizerBetweenLatticeStabilizers.lean#L17-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DatumStabilizerBetweenLatticeStabilizers.lean#L17-L24

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DatumStabilizerBetweenLatticeStabilizers
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.DatumStab
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ}

theorem GlobalTheory.HL.DatumStab.mem_smul_iff {n : ℕ} (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) (A : Submodule L.O (Fin n → E))
    (x : Fin n → E) : x ∈ g • A ↔ g.symm x ∈ A := by sorry
