-- Prove2me | Theorems.Thm_GlobalTheory_LatticeHom_eq_zero_of_forall_smul_mem
-- name    : GlobalTheory.LatticeHom.eq_zero_of_forall_smul_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:48:23.504935+00:00
-- url     : https://prove2.me/theorems/e03541ae-df3b-4bcb-9ebd-63de0709693e
-- title:
--   Lattice Hom: eq zero of forall smul mem
-- statement:
--   The Lattice Hom construction uses the eq zero of forall smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLinearEquivOfLifting.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLinearEquivOfLifting.lean#L15-L19

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ThetaUnifAVOfLaws
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLinearEquivOfLifting
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LatticeHom

theorem GlobalTheory.LatticeHom.eq_zero_of_forall_smul_mem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Λ : Submodule ℤ E) (hd : DiscreteTopology Λ) {z : E} (hz : ∀ t : ℂ, t • z ∈ Λ) : z = 0 := by sorry
