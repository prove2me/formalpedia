-- Prove2me | Theorems.Thm_GlobalTheory_ChartCmp_JetDim_tanAll_X
-- name    : GlobalTheory.ChartCmp.JetDim.tanAll_X
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:36:25.416955+00:00
-- url     : https://prove2.me/theorems/09170835-04cf-50de-8117-fadd5ca7f164
-- title:
--   Jet Dim: tan All X
-- statement:
--   The Jet Dim construction uses the tan All X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/UniversalJetCoordinatesDimUnique.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/UniversalJetCoordinatesDimUnique.lean#L31-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_UniversalJetCoordinatesDimUnique
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.JetDim
variable {V : Type} [CommRing V]

theorem GlobalTheory.ChartCmp.JetDim.tanAll_X (κ : Type) [DecidableEq κ] (i : κ) :
    tanAll (V := V) κ (Ideal.Quotient.mk _ (MvPolynomial.X i)) = TrivSqZeroExt.inr (Pi.single i (1 : V)) := by sorry
