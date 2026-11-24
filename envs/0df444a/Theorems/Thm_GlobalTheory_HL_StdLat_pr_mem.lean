-- Prove2me | Theorems.Thm_GlobalTheory_HL_StdLat_pr_mem
-- name    : GlobalTheory.HL.StdLat.pr_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:16:03.812748+00:00
-- url     : https://prove2.me/theorems/5211e73b-91db-4998-9998-6ad8ff7f2085
-- title:
--   Std Lat: pr mem
-- statement:
--   The Std Lat construction uses the pr mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemPerpSpan.lean#L196-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemPerpSpan.lean#L196-L199

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
variable {A : Submodule L.O (Fin n → E)}
variable (hXA : ∀ x ∈ Submodule.span E (Set.range e), x ∈ A)
  (hAp : ∀ x ∈ A, ∀ j, hf L Hm x (e j) = 0)
  (hd : ∀ y, (∀ j, hf L Hm y (e j) = 0) → ((∀ x ∈ A, hf L Hm x y ∈ L.O) ↔ y ∈ A))
omit hH hes
include hXA hAp

theorem GlobalTheory.HL.StdLat.pr_mem {x : Fin n → E} (hx : x ∈ A) : pr L Hm e es x ∈ A := by sorry
