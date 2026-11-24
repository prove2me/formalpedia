-- Prove2me | Theorems.Thm_GlobalTheory_TorsionCompare_substJ_zR
-- name    : GlobalTheory.TorsionCompare.substJ_zR
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:28:32.039917+00:00
-- url     : https://prove2.me/theorems/da6089fa-84bd-48dc-af55-d14afe70fa64
-- title:
--   Torsion Compare: subst J z R
-- statement:
--   The Torsion Compare construction uses the subst J z R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NotIsUnitNatCastOfIsLocalHom.lean#L104-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NotIsUnitNatCastOfIsLocalHom.lean#L104-L107

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_OriginChartMultiplication
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NotIsUnitNatCastOfIsLocalHom
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
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF GlobalTheory.IndefiniteRowSideFullHecke.OriginChartMultiplication
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TorsionCompare
variable {R : Type} [CommRing R]

theorem GlobalTheory.TorsionCompare.substJ_zR {n d : ℕ} (m : ℕ) (φ : Fin d → PS R n d)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) (q : Fin 1 × Fin d) :
    substJ m φ hφ (zR m q) = psJet m (φ q.2) := by sorry
