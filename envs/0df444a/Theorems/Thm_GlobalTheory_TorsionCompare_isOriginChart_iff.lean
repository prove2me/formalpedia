-- Prove2me | Theorems.Thm_GlobalTheory_TorsionCompare_isOriginChart_iff
-- name    : GlobalTheory.TorsionCompare.isOriginChart_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:42:45.400325+00:00
-- url     : https://prove2.me/theorems/752935fb-cbb2-4c66-9879-42bc3fed4082
-- title:
--   Torsion Compare: is Origin Chart iff
-- statement:
--   The Torsion Compare construction uses the is Origin Chart iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NotIsUnitNatCastOfIsLocalHom.lean#L249-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NotIsUnitNatCastOfIsLocalHom.lean#L249-L251

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

theorem GlobalTheory.TorsionCompare.isOriginChart_iff (F : FGLaw R d) (x : ∀ m : ℕ, algOver R (JetR R (Fin d) m) ⟶ G) :
    IsOriginChart G x F ↔ IsChartJ G F ((chartEquiv G d).symm x) := by sorry
