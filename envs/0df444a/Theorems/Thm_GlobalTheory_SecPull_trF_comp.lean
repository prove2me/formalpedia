-- Prove2me | Theorems.Thm_GlobalTheory_SecPull_trF_comp
-- name    : GlobalTheory.SecPull.trF_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:54:46.984062+00:00
-- url     : https://prove2.me/theorems/d62a627a-3474-480c-b0eb-db6f28b1fe39
-- title:
--   Sec Pull: tr F comp
-- statement:
--   The Sec Pull construction uses the tr F comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsUniqueSecPull.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsUniqueSecPull.lean#L24-L27

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SecPull
variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

theorem GlobalTheory.SecPull.trF_comp {Z : Scheme.{0}} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {h : Y' ⟶ Y}
    (hc : ∀ κ, φ' κ ≫ F = h ≫ φ κ) (ε : K → ℤ) (r : Z ⟶ Y') (z : Z) (p p' : K → L.ι) :
    trF φ ε (r ≫ h) z p p' = trF (fun k => φ' k ≫ F) ε r z p p' := by sorry
