-- Prove2me | Theorems.Thm_GlobalTheory_FinOf_finOf_tangent
-- name    : GlobalTheory.FinOf.finOf_tangent
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:44:53.780519+00:00
-- url     : https://prove2.me/theorems/d0d189e4-3101-42a9-b9e9-288296145cbf
-- title:
--   Fin Of: fin Of tangent
-- statement:
--   The Fin Of construction uses the fin Of tangent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FinOfLocalAlgebraMap.lean#L55-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FinOfLocalAlgebraMap.lean#L55-L79

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FinOfLocalAlgebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FinOf
variable {R₀ : Type} [CommRing R₀]

theorem GlobalTheory.FinOf.finOf_tangent (B : BX R₀) (p : ℕ) (hp : p ≠ 0) (C : Type) [Field C] [CharZero C]
    [Algebra R₀ C] (z z' : B.G ⟨DualNumber C⟩) (hz : p • z = 0) (hz' : p • z' = 0)
    (h : B.map (finOf_fst C) z = B.map (finOf_fst C) z') : z = z' := by sorry
