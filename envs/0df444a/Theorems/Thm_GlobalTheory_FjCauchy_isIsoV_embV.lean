-- Prove2me | Theorems.Thm_GlobalTheory_FjCauchy_isIsoV_embV
-- name    : GlobalTheory.FjCauchy.isIsoV_embV
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:59:11.425752+00:00
-- url     : https://prove2.me/theorems/9a0b1a1a-3dea-4af8-9608-f0d418eaf910
-- title:
--   Fj Cauchy: is Iso V emb V
-- statement:
--   The Fj Cauchy construction uses the is Iso V emb V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FjCauchyBound.lean#L19-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FjCauchyBound.lean#L19-L25

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowDomainCriterionHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HolomorphicPeriodicityExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMajorantFlags
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowCoefficientBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspCoefficientFlow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FjFlow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FjCauchyBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory GlobalTheory.FjCauchy
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
open NumberField Complex Filter Topology
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r)

theorem GlobalTheory.FjCauchy.isIsoV_embV {ξ : Fin r → E} (hξ : X.IsIso ξ) :
    X.IsIsoV (X.embV ξ) := by sorry
