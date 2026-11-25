-- Prove2me | Theorems.Thm_GlobalTheory_FinOf_finOf_free
-- name    : GlobalTheory.FinOf.finOf_free
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:44:57.643294+00:00
-- url     : https://prove2.me/theorems/afef727c-6e3f-4ff6-b905-9f357be4bdcd
-- title:
--   Fin Of: fin Of free
-- statement:
--   The Fin Of construction uses the fin Of free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FinOfLocalAlgebraMap.lean#L81-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FinOfLocalAlgebraMap.lean#L81-L97

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

theorem GlobalTheory.FinOf.finOf_free {O A : Type} [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A]
    [Module.Free O A] [Module.Finite O A] {n : ℕ} (ε : Fin n → A)
    (hε : CompleteOrthogonalIdempotents ε) :
    (∀ i, Module.Free O (A ⧸ Ideal.span {1 - ε i})) ∧
      (∑ i, Module.finrank O (A ⧸ Ideal.span {1 - ε i})) = Module.finrank O A := by sorry
