-- Prove2me | Theorems.Thm_GlobalTheory_ChartCmp_JetDim_exists_surjective
-- name    : GlobalTheory.ChartCmp.JetDim.exists_surjective
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:58:46.146355+00:00
-- url     : https://prove2.me/theorems/2a778220-636d-58a8-9265-5167b608e280
-- title:
--   Jet Dim: exists surjective
-- statement:
--   The Jet Dim construction uses the exists surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/UniversalJetCoordinatesDimUnique.lean#L78-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/UniversalJetCoordinatesDimUnique.lean#L78-L91

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

theorem GlobalTheory.ChartCmp.JetDim.exists_surjective {G : Over (Sp V)} [GrpObj G] {κ κ' : Type} {z : GlobalTheory.PowGerm.JetPts G κ}
    {z' : GlobalTheory.PowGerm.JetPts G κ'} (hz : GlobalTheory.PowGerm.IsUnivJ G κ z) (hz' : GlobalTheory.PowGerm.IsUnivJ G κ' z') (m : ℕ) :
    ∃ ψ : Jet V κ' m →ₐ[V] Jet V κ m, Function.Surjective ψ := by sorry
