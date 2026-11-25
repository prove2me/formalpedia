-- Prove2me | Theorems.Thm_GlobalTheory_ValGenExtend_exists_isGen_inv
-- name    : GlobalTheory.ValGenExtend.exists_isGen_inv
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:48:22.007946+00:00
-- url     : https://prove2.me/theorems/2033b58e-6470-4ab6-857a-6b44c755b7f4
-- title:
--   Val Gen Extend: exists is Gen inv
-- statement:
--   The Val Gen Extend construction uses the exists is Gen inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GeneratorExtendsFromGenericFibreValuationRing.lean#L32-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GeneratorExtendsFromGenericFibreValuationRing.lean#L32-L43

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulSecNonzeroOnSpecialFibreStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GeneratorExtendsFromGenericFibreValuationRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.ValGenExtend

theorem GlobalTheory.ValGenExtend.exists_isGen_inv {X Y : Scheme.{0}} {I : Type} {U : I → X.Opens}
    (g g' : ∀ a b, Γ(X, U a ⊓ U b)ˣ) (hg : ∀ a b, g' a b = (g a b)⁻¹) (j : Y ⟶ X)
    (t : LB.Gen ((⟨I, U, g⟩ : LB X).pull j)) (ht : t.IsGen) :
    ∃ t' : LB.Gen ((⟨I, U, g'⟩ : LB X).pull j), t'.IsGen ∧ ∀ i : I,
      rs Y (le_pull ⟨I, U, g⟩ j (W := U i) (i := i) le_rfl) (t.s fun _ => i).val *
        rs Y (le_pull ⟨I, U, g'⟩ j (W := U i) (i := i) le_rfl) (t'.s fun _ => i).val = 1 := by sorry
