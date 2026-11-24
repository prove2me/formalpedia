-- Prove2me | Theorems.Thm_GlobalTheory_TorsionCompare_psJet_eq_jetOfSeries
-- name    : GlobalTheory.TorsionCompare.psJet_eq_jetOfSeries
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:28:00.718857+00:00
-- url     : https://prove2.me/theorems/3487799d-cc1a-4cd6-85a7-313559e9d457
-- title:
--   Torsion Compare: ps Jet eq jet Of Series
-- statement:
--   The Torsion Compare construction uses the ps Jet eq jet Of Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NotIsUnitNatCastOfIsLocalHom.lean#L89-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NotIsUnitNatCastOfIsLocalHom.lean#L89-L102

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

theorem GlobalTheory.TorsionCompare.psJet_eq_jetOfSeries {n d : ℕ} [Nonempty (Fin n × Fin d)] (m : ℕ) (f : PS R n d) :
    psJet m f = jetOfSeries m f := by sorry
