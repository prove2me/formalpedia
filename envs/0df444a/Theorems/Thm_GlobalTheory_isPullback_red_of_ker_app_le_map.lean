-- Prove2me | Theorems.Thm_GlobalTheory_isPullback_red_of_ker_app_le_map
-- name    : GlobalTheory.isPullback_red_of_ker_app_le_map
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:35:47.352561+00:00
-- url     : https://prove2.me/theorems/58bfc6b9-6d7a-533d-8406-81133b291e84
-- title:
--   Global Theory: is Pullback red of ker app le map
-- statement:
--   The Global Theory construction uses the is Pullback red of ker app le map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/KerAppEqMapAppLEOfIsPullback.lean#L34-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/KerAppEqMapAppLEOfIsPullback.lean#L34-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_KerAppEqMapAppLEOfIsPullback
import Theorems.Thm_GlobalTheory_UU_IsWt_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory

theorem GlobalTheory.isPullback_red_of_ker_app_le_map (A : Type) [CommRing A] (J : Ideal A)
    (B₀ B : Scheme.{0}) (j : B₀ ⟶ B) (s₀ : B₀ ⟶ Spec (CommRingCat.of (A ⧸ J)))
    (s : B ⟶ Spec (CommRingCat.of A)) (hj : IsClosedImmersion j) (w : j ≫ s = s₀ ≫ red J)
    (hloc : ∀ b : B, ∃ V : B.Opens, b ∈ V ∧ IsAffineOpen V ∧ RingHom.ker (j.app V).hom ≤
      J.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ s.appLE ⊤ V le_top).hom) :
    IsPullback j s₀ s (red J) := by sorry
