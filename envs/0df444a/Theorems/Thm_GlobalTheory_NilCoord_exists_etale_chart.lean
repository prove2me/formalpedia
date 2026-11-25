-- Prove2me | Theorems.Thm_GlobalTheory_NilCoord_exists_etale_chart
-- name    : GlobalTheory.NilCoord.exists_etale_chart
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T16:49:55.429958+00:00
-- url     : https://prove2.me/theorems/1736f7a1-7bf5-58c7-ad06-810b0ccaf36d
-- title:
--   Nil Coord: exists etale chart
-- statement:
--   The Nil Coord construction uses the exists etale chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/NilpotentCoordinates.lean#L101-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/NilpotentCoordinates.lean#L101-L126

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NilpotentCoordinates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.NilCoord

theorem GlobalTheory.NilCoord.exists_etale_chart {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G]
    [IsLocalRing R₀] (g : ℕ) (hG : SmoothOfRelativeDimension g G.hom) :
    ∃ (C : Chart G) (π : MvPolynomial (Fin g) R₀ →ₐ[R₀] Γ(G.left, C.U)), π.toRingHom.Etale := by sorry
