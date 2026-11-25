-- Prove2me | Theorems.Thm_GlobalTheory_ChartData_jetMap_zR
-- name    : GlobalTheory.ChartData.jetMap_zR
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T15:03:03.506563+00:00
-- url     : https://prove2.me/theorems/ff2a0379-e401-48fa-adbd-c0fe5fb724af
-- title:
--   Chart Data: jet Map z R
-- statement:
--   The Chart Data construction uses the jet Map z R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsIsChartGOfBasis.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsIsChartGOfBasis.lean#L29-L32

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_IntChartCut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsPtJ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsIsChartGOfBasis
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (FGLaw)
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.ChartData
open GlobalTheory.ChartJet (Q gen sq_gen)

theorem GlobalTheory.ChartData.jetMap_zR {S : Type} [CommRing S] {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S) (h) (s : κ) :
    (jetMap φ h : Jet S κ m →ₐ[S] Jet S κ' m) (Ideal.Quotient.mk _ (MvPolynomial.X s)) = Ideal.Quotient.mk _ (φ s) := by sorry
