-- Prove2me | Theorems.Thm_GlobalTheory_SabPullCompare_cubeLB_isLB
-- name    : GlobalTheory.SabPullCompare.cubeLB_isLB
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:36:31.771081+00:00
-- url     : https://prove2.me/theorems/c6b1f4ab-7a70-43c3-bd16-3afa4921feb1
-- title:
--   Sab Pull Compare: cube LB is LB
-- statement:
--   The Sab Pull Compare construction uses the cube LB is LB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SabBaseChangeStIffFree.lean#L44-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SabBaseChangeStIffFree.lean#L44-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_PullbackGroupAction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubicalSymmetryTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsRigidifiedIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsSymmetricIffExistsGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SabBaseChangeStIffFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.PullbackGroupAction
open scoped CategoryTheory.Obj
noncomputable section
open GlobalTheory GlobalTheory.SabPullCompare
variable {S S' : Scheme.{0}}
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem GlobalTheory.SabPullCompare.cubeLB_isLB {G T : Over S} [GrpObj G] [IsCommMonObj G] {n : ℕ} (x : Fin n → (T ⟶ G))
    {L : LB G.left} (h : L.IsLB) : (cubeLB G x L).IsLB := by sorry
