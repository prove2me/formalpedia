-- Prove2me | Theorems.Thm_GlobalTheory_HL_Eichler_hf_smul_r
-- name    : GlobalTheory.HL.Eichler.hf_smul_r
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:59:35.057799+00:00
-- url     : https://prove2.me/theorems/72878cd0-0f2e-4775-9fd0-83f9d7ab870c
-- title:
--   Eichler: hf smul r
-- statement:
--   The Eichler construction uses the hf smul r property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EichlerIsometry.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EichlerIsometry.lean#L35-L37

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Eichler
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)

theorem GlobalTheory.HL.Eichler.hf_smul_r (c : E) (a y : Fin n → E) : hf L Hm y (c • a) = L.cj c * hf L Hm y a := by sorry
