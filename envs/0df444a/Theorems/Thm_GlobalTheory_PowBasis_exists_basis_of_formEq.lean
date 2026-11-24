-- Prove2me | Theorems.Thm_GlobalTheory_PowBasis_exists_basis_of_formEq
-- name    : GlobalTheory.PowBasis.exists_basis_of_formEq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:51:24.072122+00:00
-- url     : https://prove2.me/theorems/d4927345-0c13-4f86-ae0e-cb5b88da3a90
-- title:
--   Pow Basis: exists basis of form Eq
-- statement:
--   The Pow Basis construction uses the exists basis of form Eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsBasisOfFormEq.lean#L46-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsBasisOfFormEq.lean#L46-L59

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsBasisOfFormEq
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
open GlobalTheory GlobalTheory.PowBasis

theorem GlobalTheory.PowBasis.exists_basis_of_formEq {S : Scheme.{0}} {A T : Over S} {X : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    {K K' : Type} [Fintype K] [Fintype K'] {φ : K → ((T ⊗ A).left ⟶ X)} {ε : K → ℤ}
    {φ' : K' → ((T ⊗ A).left ⟶ X)} {ε' : K' → ℤ} (h : FormEq φ ε φ' ε') {m : ℕ}
    {b : Fin m → LB.Sec (LB.LinComb L φ ε)} (hb : IsSecBasis _ b) :
    ∃ b' : Fin m → LB.Sec (LB.LinComb L φ' ε'), IsSecBasis _ b' := by sorry
