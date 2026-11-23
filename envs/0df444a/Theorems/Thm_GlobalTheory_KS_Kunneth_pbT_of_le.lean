-- Prove2me | Theorems.Thm_GlobalTheory_KS_Kunneth_pbT_of_le
-- name    : GlobalTheory.KS.Kunneth.pbT_of_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:27:55.810422+00:00
-- url     : https://prove2.me/theorems/8a65896d-53a7-40a7-8af0-8bfb93589aec
-- title:
--   Kunneth: pb T of le
-- statement:
--   The Kunneth construction uses the pb T of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/KunnethSymmProductAffineCovers.lean#L78-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/KunnethSymmProductAffineCovers.lean#L78-L81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDualFamilyModSubspace
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KunnethSymmProductAffineCovers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.Kunneth

theorem GlobalTheory.KS.Kunneth.pbT_of_le {Z Y : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} (s : Γ(Y, O₀)) {O : Z.Opens}
    (h : O ≤ f ⁻¹ᵁ O₀) : pbT f s O = (f.appLE O₀ O h).hom s := by sorry
