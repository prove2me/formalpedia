-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UniformizationClosedSplit_PrimeToLevel_not_mem_M
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.UniformizationClosedSplit.PrimeToLevel.not_mem_M
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:11:16.021666+00:00
-- url     : https://prove2.me/theorems/22f81e2f-4ac2-409c-b490-fdd228427352
-- title:
--   Prime To Level: not mem M
-- statement:
--   The Prime To Level construction uses the not mem M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/UniformizationClosedSplit.lean#L57-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/UniformizationClosedSplit.lean#L57-L63

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ChartDirectionsIntegral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_UniformizationClosedSplit
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
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.UniformizationClosedSplit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
variable {Xo c}

theorem GlobalTheory.IndefiniteRowSideFullHecke.UniformizationClosedSplit.PrimeToLevel.not_mem_M {la : HeightOneSpectrum (𝓞 c.F)} (h : PrimeToLevel c la) :
    ((l.M : ℕ) : 𝓞 c.F) ∉ la.asIdeal := by sorry
