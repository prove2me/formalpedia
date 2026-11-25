-- Prove2me | Theorems.Thm_GlobalTheory_HermOrthBasis_hf_sum_left
-- name    : GlobalTheory.HermOrthBasis.hf_sum_left
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T06:08:39.235244+00:00
-- url     : https://prove2.me/theorems/42bd9572-ea9e-43fd-a2c9-af8f9d1b82cf
-- title:
--   Herm Orth Basis: hf sum left
-- statement:
--   The Herm Orth Basis construction uses the hf sum left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LeOfPerpEqBot.lean#L35-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LeOfPerpEqBot.lean#L35-L39

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfPerpEqBot
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
open GlobalTheory GlobalTheory.HermOrthBasis
open Matrix
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)

theorem GlobalTheory.HermOrthBasis.hf_sum_left {m : ℕ} (c : Fin m → E) (x : Fin m → Fin n → E) (y : Fin n → E) :
    hf L Hm (∑ b, c b • x b) y = ∑ b, c b * hf L Hm (x b) y := by sorry
