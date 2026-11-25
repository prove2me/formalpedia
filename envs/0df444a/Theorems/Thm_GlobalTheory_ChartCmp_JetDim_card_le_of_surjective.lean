-- Prove2me | Theorems.Thm_GlobalTheory_ChartCmp_JetDim_card_le_of_surjective
-- name    : GlobalTheory.ChartCmp.JetDim.card_le_of_surjective
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:10:31.539568+00:00
-- url     : https://prove2.me/theorems/72957744-523a-43c1-8e90-9587dccff2c1
-- title:
--   Jet Dim: card le of surjective
-- statement:
--   The Jet Dim construction uses the card le of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/UniversalJetCoordinatesDimUnique.lean#L36-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/UniversalJetCoordinatesDimUnique.lean#L36-L65

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

theorem GlobalTheory.ChartCmp.JetDim.card_le_of_surjective [Nontrivial V] {κ κ' : Type} [Fintype κ] [Fintype κ'] [DecidableEq κ]
    (ψ : Jet V κ' 1 →ₐ[V] Jet V κ 1) (hψ : Function.Surjective ψ) : Fintype.card κ ≤ Fintype.card κ' := by sorry
