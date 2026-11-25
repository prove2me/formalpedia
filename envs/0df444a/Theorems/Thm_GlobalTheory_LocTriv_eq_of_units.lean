-- Prove2me | Theorems.Thm_GlobalTheory_LocTriv_eq_of_units
-- name    : GlobalTheory.LocTriv.eq_of_units
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:15:40.530464+00:00
-- url     : https://prove2.me/theorems/14a53a04-0f8f-4852-946c-eae3c03fda6b
-- title:
--   Loc Triv: eq of units
-- statement:
--   The Loc Triv construction uses the eq of units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/LocallyTrivialTorusQuotientFlatSurjectiveCosets.lean#L106-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/LocallyTrivialTorusQuotientFlatSurjectiveCosets.lean#L106-L127

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableAffineOpenFunctionsWeightGradedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LocallyTrivialTorusQuotientFlatSurjectiveCosets
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.LocTriv
variable {S : Scheme.{0}}
variable {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G] {i : splitTorus S X ⟶ G} {q : G ⟶ B}

theorem GlobalTheory.LocTriv.eq_of_units {U : G.left.Opens}
    (hU : (snd (splitTorus _ X) G).left ⁻¹ᵁ U ≤ ((fst (splitTorus _ X) G ≫ i) * snd _ G).left ⁻¹ᵁ U)
    (u : X → Γ(G.left, U)ˣ) (hu : ∀ χ, IsWt i U (u χ).val χ)
    {Z : Over S} {t t' : Z ⟶ splitTorus S X} {g : Z ⟶ G} (hg : ⊤ ≤ g.left ⁻¹ᵁ U) (h : t ≫ i = t' ≫ i) : t = t' := by sorry
