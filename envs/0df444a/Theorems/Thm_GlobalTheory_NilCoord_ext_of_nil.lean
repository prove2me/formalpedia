-- Prove2me | Theorems.Thm_GlobalTheory_NilCoord_ext_of_nil
-- name    : GlobalTheory.NilCoord.ext_of_nil
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T16:43:44.691684+00:00
-- url     : https://prove2.me/theorems/35803b0f-d688-49a4-be09-6369edecbf31
-- title:
--   Nil Coord: ext of nil
-- statement:
--   The Nil Coord construction uses the ext of nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/NilpotentCoordinates.lean#L17-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/NilpotentCoordinates.lean#L17-L48

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NilpotentCoordinates
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
open GlobalTheory GlobalTheory.NilCoord
variable {R : Type} [CommRing R] {n : ℕ} {B : Type} [CommRing B] [Algebra R B]

theorem GlobalTheory.NilCoord.ext_of_nil (π : MvPolynomial (Fin n) R →ₐ[R] B) (hπ : π.toRingHom.Etale)
    {A : Type} [CommRing A] [Algebra R A] (φ₁ φ₂ : B →ₐ[R] A)
    (h : ∀ b, IsNilpotent (φ₁ b - φ₂ b))
    (hs : ∀ j : Fin n, φ₁ (π (MvPolynomial.X j)) = φ₂ (π (MvPolynomial.X j))) : φ₁ = φ₂ := by sorry
