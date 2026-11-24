-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_JetChartLaws_jetVec_X
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.JetChartLaws.jetVec_X
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T09:42:06.89954+00:00
-- url     : https://prove2.me/theorems/0b185081-f2cc-4d1b-9fff-5a98c7ce9199
-- title:
--   Jet Chart Laws: jet Vec X
-- statement:
--   The Jet Chart Laws construction uses the jet Vec X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/JetChartLaws.lean#L93-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/JetChartLaws.lean#L93-L97

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SubConstMemOrig
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_JetChartLaws
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.JetChartLaws
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {X₀ : Scheme.{0}} {S : Type} [CommRing S]
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem GlobalTheory.IndefiniteRowSideFullHecke.JetChartLaws.jetVec_X {σ : Type} (c : σ → S) (i : σ) :
    jetVec c (Ideal.Quotient.mk _ (MvPolynomial.X i)) = c i • (DualNumber.eps : DualNumber S) := by sorry
