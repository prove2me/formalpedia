-- Prove2me | Theorems.Thm_GlobalTheory_SmoothNilLift_exists_lift_of_nil
-- name    : GlobalTheory.SmoothNilLift.exists_lift_of_nil
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:55:33.207322+00:00
-- url     : https://prove2.me/theorems/bb4dfbdf-a2e1-54fe-a00e-298f4bd5f167
-- title:
--   Smooth Nil Lift: exists lift of nil
-- statement:
--   The Smooth Nil Lift construction uses the exists lift of nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsLiftOfNil.lean#L12-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsLiftOfNil.lean#L12-L53

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsLiftOfNil
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
open GlobalTheory GlobalTheory.SmoothNilLift

theorem GlobalTheory.SmoothNilLift.exists_lift_of_nil {R A W K : Type} [CommRing R] [CommRing A] [CommRing W] [CommRing K]
    [Algebra R A] [Algebra R W] [Algebra R K] [Algebra.Smooth R A] (ρ : W →ₐ[R] K)
    (hρ : Function.Surjective ρ) (hn : ∀ a ∈ RingHom.ker ρ, IsNilpotent a) (φ : A →ₐ[R] K) :
    ∃ ψ : A →ₐ[R] W, ρ.comp ψ = φ := by sorry
