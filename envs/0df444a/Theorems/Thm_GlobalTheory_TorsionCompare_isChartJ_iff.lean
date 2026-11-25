-- Prove2me | Theorems.Thm_GlobalTheory_TorsionCompare_isChartJ_iff
-- name    : GlobalTheory.TorsionCompare.isChartJ_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:09:32.99657+00:00
-- url     : https://prove2.me/theorems/6416affe-8efc-439b-906a-2d498001be81
-- title:
--   Torsion Compare: is Chart J iff
-- statement:
--   The Torsion Compare construction uses the is Chart J iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NotIsUnitNatCastOfIsLocalHom.lean#L235-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NotIsUnitNatCastOfIsLocalHom.lean#L235-L247

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
variable {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G]
variable {d : ℕ}

theorem GlobalTheory.TorsionCompare.isChartJ_iff (F : FGLaw R d) (x : ∀ m : ℕ, algOver R (JetR R (Fin 1 × Fin d) m) ⟶ G) :
    IsChartJ G F x ↔ IsOriginChart G (chartEquiv G d x) F := by sorry
