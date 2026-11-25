-- Prove2me | Theorems.Thm_GlobalTheory_TorsionCharacter_exists_pow_mem_span
-- name    : GlobalTheory.TorsionCharacter.exists_pow_mem_span
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:43:59.782697+00:00
-- url     : https://prove2.me/theorems/776f4a54-76c1-5061-8446-257e316731de
-- title:
--   Torsion Character: exists pow mem span
-- statement:
--   The Torsion Character construction uses the exists pow mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsAlgHomValuationSubring.lean#L90-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsAlgHomValuationSubring.lean#L90-L116

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_ColValMonomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsCharactersDlogMinorsGe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowEqScaleAndExistsUniqueTorsion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_GermEvalOneStandardPointSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitsZpowSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsAlgHomValuationSubring
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TorsionCharacter
variable {O : Type} [CommRing O]
variable {F : Type} [Field F] (v : AddValuation F (WithTop ℚ))

theorem GlobalTheory.TorsionCharacter.exists_pow_mem_span (a b : TWO.Ov v) (ha : ¬ IsUnit a) (hb : b ≠ 0) :
    ∃ n : ℕ, a ^ n ∈ Ideal.span {b} := by sorry
