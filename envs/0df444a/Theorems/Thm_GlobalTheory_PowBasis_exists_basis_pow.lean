-- Prove2me | Theorems.Thm_GlobalTheory_PowBasis_exists_basis_pow
-- name    : GlobalTheory.PowBasis.exists_basis_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:08.660674+00:00
-- url     : https://prove2.me/theorems/931e87dd-8e22-48c9-b975-4542d3f892ff
-- title:
--   Pow Basis: exists basis pow
-- statement:
--   The Pow Basis construction uses the exists basis pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsBasisOfFormEq.lean#L66-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsBasisOfFormEq.lean#L66-L72

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

theorem GlobalTheory.PowBasis.exists_basis_pow (hT : SecTwistSt) {S : Scheme.{0}} (P : PolAV S) (k : ℕ) (hk : 1 ≤ k) (R : Type) [CommRing R]
    [IsLocalRing R] (t : Spec (CommRingCat.of R) ⟶ S) :
    ∃ b : Fin (k ^ P.g) → LB.Sec (LPow P.A P.L (k : ℤ) (Over.mk t)), IsSecBasis _ b := by sorry
