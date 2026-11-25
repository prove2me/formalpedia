-- Prove2me | Theorems.Thm_GlobalTheory_FibreDeriv_isDerivAt0_of_affine
-- name    : GlobalTheory.FibreDeriv.isDerivAt0_of_affine
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:58:13.72526+00:00
-- url     : https://prove2.me/theorems/4342bac3-bf66-44b1-bdeb-f93ecc5ce96d
-- title:
--   Fibre Deriv: is Deriv At0 of affine
-- statement:
--   The Fibre Deriv construction uses the is Deriv At0 of affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsDerivAt0OfIsPullback.lean#L123-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsDerivAt0OfIsPullback.lean#L123-L159

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsDerivAt0OfIsPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Filter Topology
open GlobalTheory
open GlobalTheory.FibreDeriv
variable {g : ℕ} {X Y : Scheme.{0}}

theorem GlobalTheory.FibreDeriv.isDerivAt0_of_affine {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ X}
    (h0 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0) {V : X.Opens} (hV : IsAffineOpen V)
    (hv : ⊤ ≤ v ⁻¹ᵁ V)
    (H : ∀ a : Γ(X, V), DifferentiableAt ℂ (fun z => valAt' (e z) V a) 0 ∧
      evEps v V hv a = jet w (fun z => valAt' (e z) V a)) : IsDerivAt0 e w v := by sorry
