-- Prove2me | Theorems.Thm_GlobalTheory_EtaCard_card_levGrp_and_span
-- name    : GlobalTheory.EtaCard.card_levGrp_and_span
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:05:41.865264+00:00
-- url     : https://prove2.me/theorems/d6b479ac-fa5d-450d-91c6-9a79aba1b1da
-- title:
--   Eta Card: card lev Grp and span
-- statement:
--   The Eta Card construction uses the card lev Grp and span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CardLevGrpAndSpan.lean#L84-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CardLevGrpAndSpan.lean#L84-L130

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_IsNullVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_TwoMulPowFourDvdCardGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CardLevGrpAndSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.EtaForm
attribute [local instance] Over.cartesianMonoidalCategory
open scoped TensorProduct
open GlobalTheory GlobalTheory.EtaCard
variable (E : Type) [Field E] [NumberField E]

theorem GlobalTheory.EtaCard.card_levGrp_and_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (R : ℕ), 1 < R → Finite (LevGrp Dw (R ^ 4)) ∧ Finite (LatMod Dw R) ∧ Nat.card (LatMod Dw R) = R ^ (2 * FD.fdeg E * (Dw.p + Dw.q)) ∧ Nat.card (LevGrp Dw (R ^ 4)) ≤ R ^ (8 * FD.fdeg E * (Dw.p + Dw.q) ^ 2) ∧ (Odd R → 2 ≤ Dw.p + Dw.q → 2 * R ^ 4 ∣ Nat.card (LevGrp Dw (R ^ 4))) ∧ (∃ x₀ : Fin (Dw.p + Dw.q) → Dw.La, Submodule.span (𝓞 E) (Set.range x₀) ⊔ (Ideal.span {(R : 𝓞 E)} • ⊤) = ⊤) ∧ ∀ (n : ℕ) (x₀ : Fin n → Dw.La), Submodule.span (𝓞 E) (Set.range x₀) ⊔ (Ideal.span {(R : 𝓞 E)} • ⊤) = ⊤ → ∀ (y : Fin n → LatMod Dw R) (g : LevGrp Dw (R ^ 4)), Submodule.span (𝓞 E) (Set.range fun b => g (shiftFam R x₀ y b)) = ⊤ := by sorry
