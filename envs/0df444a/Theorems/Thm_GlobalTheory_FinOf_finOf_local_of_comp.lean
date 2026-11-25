-- Prove2me | Theorems.Thm_GlobalTheory_FinOf_finOf_local_of_comp
-- name    : GlobalTheory.FinOf.finOf_local_of_comp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:43:19.749065+00:00
-- url     : https://prove2.me/theorems/5c4ece9b-7985-581a-9eff-8c7fef2e0801
-- title:
--   Fin Of: fin Of local of comp
-- statement:
--   The Fin Of construction uses the fin Of local of comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FinOfLocalAlgebraMap.lean#L23-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FinOfLocalAlgebraMap.lean#L23-L31

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

theorem GlobalTheory.FinOf.finOf_local_of_comp {O Q S : Type} [CommRing O] [CommRing Q] [CommRing S] [IsLocalRing O]
    [IsLocalRing Q] [IsLocalRing S] [Algebra O Q] [Algebra.IsIntegral O Q] (g : Q →+* S)
    (h : IsLocalHom (g.comp (algebraMap O Q))) : IsLocalHom g := by sorry
