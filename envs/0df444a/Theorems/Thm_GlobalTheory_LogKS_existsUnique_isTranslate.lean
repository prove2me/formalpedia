-- Prove2me | Theorems.Thm_GlobalTheory_LogKS_existsUnique_isTranslate
-- name    : GlobalTheory.LogKS.existsUnique_isTranslate
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:14:16.234155+00:00
-- url     : https://prove2.me/theorems/43c2149b-9ba1-5a61-b569-111b86fbc688
-- title:
--   Log KS: exists Unique is Translate
-- statement:
--   The Log KS construction uses the exists Unique is Translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/DenseInterior.lean#L60-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/DenseInterior.lean#L60-L74

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

theorem GlobalTheory.LogKS.existsUnique_isTranslate {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {x : Sp R ⟶ X}
    {g : Sp S ⟶ t.G.left} (hg : g ≫ t.G.hom = spMap φ ≫ x) {v : Sp (DualNumber R) ⟶ t.G.left}
    (hv : IsTanAtG t x v) : ∃! w, IsTranslate t φ g v w := by sorry
