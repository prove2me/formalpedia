-- Prove2me | Theorems.Thm_GlobalTheory_LGrp_IsZonal_one_and_biinv
-- name    : GlobalTheory.LGrp.IsZonal.one_and_biinv
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:17:44.859543+00:00
-- url     : https://prove2.me/theorems/e55d0283-ed60-5e11-aaa5-376fb1839902
-- title:
--   Is Zonal: one and biinv
-- statement:
--   The Is Zonal construction uses the one and biinv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean#L65-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean#L65-L70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped NNReal TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.LGrp
open GlobalTheory.PRep
variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem GlobalTheory.LGrp.IsZonal.one_and_biinv {ρ : Representation ℂ G V} {K : Subgroup G} {ω : G → ℂ} (h : IsZonal ρ K ω) :
    ω 1 = 1 ∧ ∀ k₁ ∈ K, ∀ k₂ ∈ K, ∀ g, ω (k₁ * g * k₂) = ω g := by sorry
