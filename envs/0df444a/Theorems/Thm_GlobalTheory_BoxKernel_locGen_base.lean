-- Prove2me | Theorems.Thm_GlobalTheory_BoxKernel_locGen_base
-- name    : GlobalTheory.BoxKernel.locGen_base
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:50:25.087655+00:00
-- url     : https://prove2.me/theorems/f893e76c-fb80-5aec-bbc3-e5c39f5e5135
-- title:
--   Box Kernel: loc Gen base
-- statement:
--   The Box Kernel construction uses the loc Gen base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/KTrivExternalTensorPowerLineBundle.lean#L46-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/KTrivExternalTensorPowerLineBundle.lean#L46-L51

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_LocGenOfTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_KTrivExternalTensorPowerLineBundle
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.BoxKernel
open GlobalTheory.KerPow
variable {X X' Y B : Scheme.{0}} {L : LB X} {K J : Type} [Fintype K] [Fintype J]

theorem GlobalTheory.BoxKernel.locGen_base (hL : L.IsLB) (π : Y ⟶ B) (b : K → (B ⟶ X)) (ε : K → ℤ) :
    LocGen L π (fun k => π ≫ b k) ε := by sorry
