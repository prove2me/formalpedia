-- Prove2me | Theorems.Thm_GlobalTheory_HostModel_coeff_F_le_iff
-- name    : GlobalTheory.HostModel.coeff_F_le_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:19:37.604052+00:00
-- url     : https://prove2.me/theorems/a8aa09ca-8456-5b96-9e4c-9327d1f8b505
-- title:
--   Host Model: coeff F le iff
-- statement:
--   The Host Model construction uses the coeff F le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/SqrtNegDiscMemCoeffField.lean#L71-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/SqrtNegDiscMemCoeffField.lean#L71-L79

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LevelOfSplitAndLevelCoeffExist
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_SqrtNegDiscMemCoeffField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HostModel
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem GlobalTheory.HostModel.coeff_F_le_iff (l : Level H) (F : IntermediateField ℚ ℂ) :
    (coeff l).F ≤ F ↔ zeta l.M' ∈ F ∧ ∀ (τ : E →+* ℂ) (a : E), τ a ∈ F := by sorry
