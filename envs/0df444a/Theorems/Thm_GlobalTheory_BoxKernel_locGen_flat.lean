-- Prove2me | Theorems.Thm_GlobalTheory_BoxKernel_locGen_flat
-- name    : GlobalTheory.BoxKernel.locGen_flat
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:41:10.739058+00:00
-- url     : https://prove2.me/theorems/91ff72ca-359d-4835-8ac3-6bdada1f54fc
-- title:
--   Box Kernel: loc Gen flat
-- statement:
--   The Box Kernel construction uses the loc Gen flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/KTrivExternalTensorPowerLineBundle.lean#L53-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/KTrivExternalTensorPowerLineBundle.lean#L53-L58

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

theorem GlobalTheory.BoxKernel.locGen_flat (F : J → (X' ⟶ X)) {π : Y ⟶ B} {ψ : K → (Y ⟶ X')} {ε : K → ℤ}
    (H : LocGen (LB.LinComb L F (fun _ => 1)) π ψ ε) :
    LocGen L (K := K × J) π (fun q => ψ q.1 ≫ F q.2) (fun q => ε q.1) := by sorry
