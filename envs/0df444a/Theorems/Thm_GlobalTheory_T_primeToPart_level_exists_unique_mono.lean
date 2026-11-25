-- Prove2me | Theorems.Thm_GlobalTheory_T_primeToPart_level_exists_unique_mono
-- name    : GlobalTheory.T.primeToPart_level_exists_unique_mono
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:36:35.250415+00:00
-- url     : https://prove2.me/theorems/8c1fe79a-a117-533f-9b78-99c72cd322e8
-- title:
--   T: prime To Part level exists unique mono
-- statement:
--   The T construction uses the prime To Part level exists unique mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/PrimeToPartLevelExistsUniqueMonoStatement.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/PrimeToPartLevelExistsUniqueMonoStatement.lean#L13-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PrimeToPartLevelExistsUniqueMono
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_AuxiliaryInertOddPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PrimeToPartLevelExistsUniqueMonoStatement
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
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

theorem GlobalTheory.T.primeToPart_level_exists_unique_mono : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (p : ℕ), p.Prime → (∀ l : Level H, l.GoodAt p → ∃ l₀ : Level H, IsPrimeToPart l₀ l p) ∧ (∀ l l₀ : Level H, IsPrimeToPart l₀ l p → l₀.Dvd l ∧ l₀.M.Coprime p ∧ ∀ l₀' : Level H, IsPrimeToPart l₀' l p → l₀' = l₀) ∧ ∀ l l' l₀ l₀' : Level H, IsPrimeToPart l₀ l p → IsPrimeToPart l₀' l' p → l.Dvd l' → l₀.Dvd l₀' := by sorry
