-- Prove2me | Theorems.Thm_GlobalTheory_SabPullCompare_lbIso_cubeLB
-- name    : GlobalTheory.SabPullCompare.lbIso_cubeLB
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:17:00.423739+00:00
-- url     : https://prove2.me/theorems/ed3f2814-e915-4e21-875e-de0accfc79a2
-- title:
--   Sab Pull Compare: lb Iso cube LB
-- statement:
--   The Sab Pull Compare construction uses the lb Iso cube LB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SabBaseChangeStIffFree.lean#L39-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SabBaseChangeStIffFree.lean#L39-L42

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

theorem GlobalTheory.SabPullCompare.lbIso_cubeLB {G T : Over S} [GrpObj G] [IsCommMonObj G] {n : ℕ} (x : Fin n → (T ⟶ G))
    {L M : LB G.left} (h : LBIso L M) : LBIso (cubeLB G x L) (cubeLB G x M) := by sorry
