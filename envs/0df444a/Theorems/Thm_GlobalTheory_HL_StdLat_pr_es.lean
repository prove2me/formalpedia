-- Prove2me | Theorems.Thm_GlobalTheory_HL_StdLat_pr_es
-- name    : GlobalTheory.HL.StdLat.pr_es
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:16:07.83092+00:00
-- url     : https://prove2.me/theorems/86f4c575-4e6c-485d-bb23-5d74667e64c5
-- title:
--   Std Lat: pr es
-- statement:
--   The Std Lat construction uses the pr es property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemPerpSpan.lean#L101-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemPerpSpan.lean#L101-L102

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.StdLat
open GlobalTheory.HL.Eichler
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
variable {L Hm} {r : ℕ} {e es : Fin r → Fin n → E} (hH : IsHerm L Hm)
  (hee : ∀ i j, hf L Hm (e i) (e j) = 0) (hss : ∀ i j, hf L Hm (es i) (es j) = 0)
  (hes : ∀ i j, hf L Hm (e i) (es j) = if i = j then 1 else 0)
include hH hes
omit hH
include hss

theorem GlobalTheory.HL.StdLat.pr_es (x : Fin n → E) (j : Fin r) : hf L Hm (pr L Hm e es x) (es j) = 0 := by sorry
