-- Prove2me | Theorems.Thm_GlobalTheory_PowBasis_exists_basis_pow_field
-- name    : GlobalTheory.PowBasis.exists_basis_pow_field
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:17:26.351906+00:00
-- url     : https://prove2.me/theorems/5ff8bdf2-5ed9-4c3d-88bc-9bd51b79c2d8
-- title:
--   Pow Basis: exists basis pow field
-- statement:
--   The Pow Basis construction uses the exists basis pow field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsBasisOfFormEq.lean#L74-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsBasisOfFormEq.lean#L74-L86

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

theorem GlobalTheory.PowBasis.exists_basis_pow_field : SecTwistSt → ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∃ b : Fin (k ^ A.g) → LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F)), ∀ t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F)), ∃! c : Fin (k ^ A.g) → F, ∀ j, t.f j = ∑ i, liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i)) * (b i).f j := by sorry
