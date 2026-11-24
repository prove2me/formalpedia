-- Prove2me | Theorems.Thm_GlobalTheory_HL_Eichler_eich_inv
-- name    : GlobalTheory.HL.Eichler.eich_inv
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T14:00:06.706288+00:00
-- url     : https://prove2.me/theorems/e2fc9794-833c-490b-b15b-f91043e9e20d
-- title:
--   Eichler: eich inv
-- statement:
--   The Eichler construction uses the eich inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EichlerIsometry.lean#L53-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EichlerIsometry.lean#L53-L58

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

theorem GlobalTheory.HL.Eichler.eich_inv {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm) (x u : Fin n → E) (s : E)
    (hx : hf L Hm x x = 0) (hu : hf L Hm u x = 0) (hs : s + L.cj s = hf L Hm u u) (v : Fin n → E) :
    eich L Hm x (-u) (L.cj s) (eich L Hm x u s v) = v := by sorry
