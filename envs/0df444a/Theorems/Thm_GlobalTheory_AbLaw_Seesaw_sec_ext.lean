-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_Seesaw_sec_ext
-- name    : GlobalTheory.AbLaw.Seesaw.sec_ext
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:06:55.739727+00:00
-- url     : https://prove2.me/theorems/2dcebdfd-1499-4e7a-8a56-6075d4adb4a2
-- title:
--   Seesaw: sec ext
-- statement:
--   The Seesaw construction uses the sec ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsKernelVector.lean#L96-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsKernelVector.lean#L96-L114

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsKernelVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.Seesaw
variable {X X' Y : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']

theorem GlobalTheory.AbLaw.Seesaw.sec_ext {N : LB Y} (s s' : LB.Sec N) {I : Type} (V : I → Y.Opens) (c : I → N.ι)
    (le : ∀ i, V i ≤ N.U (c i)) (hV : ∀ y, ∃ i, y ∈ V i)
    (h : ∀ i, rs Y (le i) (s.f (c i)) = rs Y (le i) (s'.f (c i))) : s = s' := by sorry
