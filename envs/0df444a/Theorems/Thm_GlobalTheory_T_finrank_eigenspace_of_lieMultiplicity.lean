-- Prove2me | Theorems.Thm_GlobalTheory_T_finrank_eigenspace_of_lieMultiplicity
-- name    : GlobalTheory.T.finrank_eigenspace_of_lieMultiplicity
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:10:34.27727+00:00
-- url     : https://prove2.me/theorems/ce1775a3-db5f-4a9c-970f-735d365af1d0
-- title:
--   T: finrank eigenspace of lie Multiplicity
-- statement:
--   The T construction uses the finrank eigenspace of lie Multiplicity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/FinrankEigenspaceOfLieMultiplicityStatement.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/FinrankEigenspaceOfLieMultiplicityStatement.lean#L12-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FinrankEigenspaceOfLieMultiplicity
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FinrankEigenspaceOfLieMultiplicityStatement
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

theorem GlobalTheory.T.finrank_eigenspace_of_lieMultiplicity : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (O : Type) [CommRing O] (act : OAct O P₀.A) (F : O → Module.End ℂ (Fin P₀.g → ℂ)), (∀ a z, u.ex (F a z) = u.ex z ≫ act.act a) → ∀ (τ : O →+* ℂ) (n : ℕ), LieMult act (𝟙 _) τ n → Module.finrank ℂ ↥(⨅ a, Module.End.eigenspace (F a) (τ a)) = n := by sorry
