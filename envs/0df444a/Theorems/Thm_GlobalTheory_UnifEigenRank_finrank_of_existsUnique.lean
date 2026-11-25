-- Prove2me | Theorems.Thm_GlobalTheory_UnifEigenRank_finrank_of_existsUnique
-- name    : GlobalTheory.UnifEigenRank.finrank_of_existsUnique
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:39:42.907401+00:00
-- url     : https://prove2.me/theorems/2fc8fc3c-ff3b-4a44-ab75-ca081dcb9de0
-- title:
--   Unif Eigen Rank: finrank of exists Unique
-- statement:
--   The Unif Eigen Rank construction uses the finrank of exists Unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/FinrankEigenspaceOfLieMultiplicity.lean#L18-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/FinrankEigenspaceOfLieMultiplicity.lean#L18-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsPushEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLieBasisOfHolUnif
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FinrankEigenspaceOfLieMultiplicity
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
open GlobalTheory GlobalTheory.UnifEigenRank

theorem GlobalTheory.UnifEigenRank.finrank_of_existsUnique {k V : Type} [Field k] [AddCommGroup V] [Module k V] (E : Submodule k V) {n : ℕ}
    (W : Fin n → V) (hW : ∀ i, W i ∈ E) (h : ∀ z ∈ E, ∃! c : Fin n → k, z = ∑ i, c i • W i) :
    Module.finrank k E = n := by sorry
