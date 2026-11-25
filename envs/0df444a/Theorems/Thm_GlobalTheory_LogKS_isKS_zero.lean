-- Prove2me | Theorems.Thm_GlobalTheory_LogKS_isKS_zero
-- name    : GlobalTheory.LogKS.isKS_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:14:02.830819+00:00
-- url     : https://prove2.me/theorems/eaa77295-cfbc-5659-b622-d8540d29ea33
-- title:
--   Log KS: is KS zero
-- statement:
--   The Log KS construction uses the is KS zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/DenseInterior.lean#L92-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/DenseInterior.lean#L92-L97

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsChartIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__DenseInterior_23def473f6482931
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped Matrix
open GlobalTheory GlobalTheory.LogKS
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)

theorem GlobalTheory.LogKS.isKS_zero (V : X.Opens) (U : X.affineOpens) {n : ℕ}
    (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) : IsKS t V U v (fun _ => 0) 0 := by sorry
