-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_Seesaw_triv_of_loc
-- name    : GlobalTheory.AbLaw.Seesaw.triv_of_loc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:08:56.983936+00:00
-- url     : https://prove2.me/theorems/ca208876-ddbb-48d4-95ff-c4d707b1633f
-- title:
--   Seesaw: triv of loc
-- statement:
--   The Seesaw construction uses the triv of loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsKernelVector.lean#L169-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsKernelVector.lean#L169-L177

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
variable {f : X ⟶ Spec (CommRingCat.of R)} {M : LB X} (P : Perf f M)
variable {g : R →+* R'} {π : X' ⟶ X} {f' : X' ⟶ Spec (CommRingCat.of R')}
  (h : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
include h

theorem GlobalTheory.AbLaw.Seesaw.triv_of_loc (v : Fin P.a → R') (hv : (P.D₀.map g).mulVec v = 0)
    (H : ∀ y : X', ∃ i, y ∈ X'.basicOpen (loc P π f' v i)) : Triv (M.pull π) := by sorry
