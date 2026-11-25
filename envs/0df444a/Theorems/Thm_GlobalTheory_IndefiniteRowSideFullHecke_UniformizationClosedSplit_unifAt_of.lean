-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UniformizationClosedSplit_unifAt_of
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.UniformizationClosedSplit.unifAt_of
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:11:00.879603+00:00
-- url     : https://prove2.me/theorems/6ac033a3-5f5d-546d-b299-c6f66d1325e8
-- title:
--   Uniformization Closed Split: unif At of
-- statement:
--   The Uniformization Closed Split construction uses the unif At of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/UniformizationClosedSplit.lean#L51-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/UniformizationClosedSplit.lean#L51-L52

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.UniformizationClosedSplit.unifAt_of (h₁ : ModelAt Xo c) (h₂ : UnifOfModel Xo c) : UnifAt Xo c := by sorry
