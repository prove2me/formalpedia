-- Prove2me | Theorems.Thm_GlobalTheory_EtaCard_span_sup_pow
-- name    : GlobalTheory.EtaCard.span_sup_pow
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:59:55.255802+00:00
-- url     : https://prove2.me/theorems/e1a3aa49-2153-4065-be89-19e0215a9101
-- title:
--   Eta Card: span sup pow
-- statement:
--   The Eta Card construction uses the span sup pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CardLevGrpAndSpan.lean#L52-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CardLevGrpAndSpan.lean#L52-L61

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

theorem GlobalTheory.EtaCard.span_sup_pow (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (a : O) (S : Submodule O M)
    (h : S ⊔ Ideal.span {a} • ⊤ = ⊤) (k : ℕ) : S ⊔ Ideal.span {a ^ k} • ⊤ = ⊤ := by sorry
