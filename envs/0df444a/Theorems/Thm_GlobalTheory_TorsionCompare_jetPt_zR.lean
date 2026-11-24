-- Prove2me | Theorems.Thm_GlobalTheory_TorsionCompare_jetPt_zR
-- name    : GlobalTheory.TorsionCompare.jetPt_zR
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:10:04.466199+00:00
-- url     : https://prove2.me/theorems/84c9ca0d-9d70-4100-b1bf-0075900a093d
-- title:
--   Torsion Compare: jet Pt z R
-- statement:
--   The Torsion Compare construction uses the jet Pt z R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NotIsUnitNatCastOfIsLocalHom.lean#L117-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NotIsUnitNatCastOfIsLocalHom.lean#L117-L121

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

theorem GlobalTheory.TorsionCompare.jetPt_zR {n d : ℕ} (i : Fin n) (m : ℕ) (q : Fin 1 × Fin d) :
    jetPt (T := R) i m (zR m q) = zR m (i, q.2) := by sorry
