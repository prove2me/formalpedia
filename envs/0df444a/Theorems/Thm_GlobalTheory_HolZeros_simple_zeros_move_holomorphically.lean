-- Prove2me | Theorems.Thm_GlobalTheory_HolZeros_simple_zeros_move_holomorphically
-- name    : GlobalTheory.HolZeros.simple_zeros_move_holomorphically
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T17:37:00.136322+00:00
-- url     : https://prove2.me/theorems/1e675ae8-7f1c-4e1e-a8a6-f6a9740503bb
-- title:
--   Hol Zeros: simple zeros move holomorphically
-- statement:
--   The Hol Zeros construction uses the simple zeros move holomorphically property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/SimpleZerosMoveHolomorphically.lean#L161-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/SimpleZerosMoveHolomorphically.lean#L161-L258

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_LevBasis
import Definitions.Def_Development_AbelianVarietyTheory_Statements_ThetaLevelCharacters_MemThetaLevelCharDimZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KaRuleK
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SimpleZerosMoveHolomorphically
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open Filter Topology
open GlobalTheory GlobalTheory.HolZeros

theorem GlobalTheory.HolZeros.simple_zeros_move_holomorphically :
    ∀ (g n d : ℕ) (a b : Fin g → ℂ) (F : Fin g → (Fin g → Fin g → ℂ) → (Fin g → ℂ) → ℂ) (p₀ : (Fin g → Fin g → ℂ)) (z₀ : Fin d → Fin g → ℂ), p₀ ∈ Key.phDom g → (∀ i, HolFam (Key.phDom g) (F i)) → (∀ i, ∀ p ∈ Key.phDom g, IsLevel (per p) a b n (F i p)) → let Good : (Fin g → Fin g → ℂ) → (Fin d → Fin g → ℂ) → Prop := fun p z => (∀ e i, F i p (z e) = 0) ∧ (∀ e, (Matrix.of fun i k => fderiv ℂ (F i p) (z e) (Pi.single k 1)).det ≠ 0) ∧ (∀ e e' (m m' : Fin g → ℤ), z e = z e' + ((fun i => (m i : ℂ)) + (per p).mulVec (fun i => (m' i : ℂ))) → e = e') ∧ ∀ y, (∀ i, F i p y = 0) → ∃ (e : Fin d) (m m' : Fin g → ℤ), y = z e + ((fun i => (m i : ℂ)) + (per p).mulVec (fun i => (m' i : ℂ))); Good p₀ z₀ → ∃ (W : Set (Fin g → Fin g → ℂ)) (z : (Fin g → Fin g → ℂ) → Fin d → Fin g → ℂ), IsOpen W ∧ p₀ ∈ W ∧ W ⊆ Key.phDom g ∧ z p₀ = z₀ ∧ DifferentiableOn ℂ z W ∧ ∀ p ∈ W, Good p (z p) := by sorry
