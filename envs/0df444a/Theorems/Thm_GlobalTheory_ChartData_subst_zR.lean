-- Prove2me | Theorems.Thm_GlobalTheory_ChartData_subst_zR
-- name    : GlobalTheory.ChartData.subst_zR
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:00:08.363021+00:00
-- url     : https://prove2.me/theorems/7230e8f8-ba21-48f5-b4f1-55a971b0084e
-- title:
--   Chart Data: subst z R
-- statement:
--   The Chart Data construction uses the subst z R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsIsChartGOfBasis.lean#L34-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsIsChartGOfBasis.lean#L34-L36

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

theorem GlobalTheory.ChartData.subst_zR {S : Type} [CommRing S] {d n : ℕ} (m : ℕ) (p : Q S d n) (s : Fin 1 × Fin d) :
    jetSubstP m (fun s : Fin 1 × Fin d => psTrunc m (p.1 s.2)) (Chart.zR m s) = ChartJet.pj m (p.1 s.2) := by sorry
