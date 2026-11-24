-- Prove2me | Theorems.Thm_GlobalTheory_Models_primeToPart_spec
-- name    : GlobalTheory.Models.primeToPart_spec
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:27:10.008644+00:00
-- url     : https://prove2.me/theorems/3147be1a-6f40-40a5-8b89-307650584ed8
-- title:
--   Models: prime To Part spec
-- statement:
--   The Models construction uses the prime To Part spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/PrimeToPartLevelExistsUniqueMono.lean#L81-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/PrimeToPartLevelExistsUniqueMono.lean#L81-L113

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_AuxiliaryInertOddPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PrimeToPartLevelExistsUniqueMono
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
open GlobalTheory GlobalTheory.Models
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct Pointwise
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem GlobalTheory.Models.primeToPart_spec : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (p : ℕ), p.Prime →
    (∀ l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H, l.GoodAt p → ∃ l₀ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H, _root_.GlobalTheory.Models.IsPrimeToPart l₀ l p) ∧
    (∀ l l₀ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H, _root_.GlobalTheory.Models.IsPrimeToPart l₀ l p → l₀.Dvd l ∧ l₀.M.Coprime p ∧
      ∀ l₀' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H, _root_.GlobalTheory.Models.IsPrimeToPart l₀' l p → l₀' = l₀) ∧
    ∀ l l' l₀ l₀' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H, _root_.GlobalTheory.Models.IsPrimeToPart l₀ l p → _root_.GlobalTheory.Models.IsPrimeToPart l₀' l' p → l.Dvd l' →
      l₀.Dvd l₀' := by sorry
