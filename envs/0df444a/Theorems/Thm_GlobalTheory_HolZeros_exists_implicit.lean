-- Prove2me | Theorems.Thm_GlobalTheory_HolZeros_exists_implicit
-- name    : GlobalTheory.HolZeros.exists_implicit
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T17:31:11.366562+00:00
-- url     : https://prove2.me/theorems/11ee94b1-1be0-436f-a778-33bd4ed29409
-- title:
--   Hol Zeros: exists implicit
-- statement:
--   The Hol Zeros construction uses the exists implicit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/SimpleZerosMoveHolomorphically.lean#L89-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/SimpleZerosMoveHolomorphically.lean#L89-L143

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

theorem GlobalTheory.HolZeros.exists_implicit {g : ℕ} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    [CompleteSpace P] (F : Fin g → P → (Fin g → ℂ) → ℂ) (p₀ : P) (z₀ : Fin g → ℂ)
    (hF : ∀ i, ContDiffAt ℂ 1 (fun q : P × (Fin g → ℂ) => F i q.1 q.2) (p₀, z₀))
    (h0 : ∀ i, F i p₀ z₀ = 0)
    (hd : (Matrix.of fun i k => fderiv ℂ (F i p₀) z₀ (Pi.single k 1)).det ≠ 0) :
    ∃ z : P → Fin g → ℂ, z p₀ = z₀ ∧ (∀ᶠ p in 𝓝 p₀, DifferentiableAt ℂ z p) ∧
      (∀ᶠ p in 𝓝 p₀, ∀ i, F i p (z p) = 0) ∧
      (∀ᶠ p in 𝓝 p₀, (Matrix.of fun i k => fderiv ℂ (F i p) (z p) (Pi.single k 1)).det ≠ 0) ∧
      ∀ᶠ q in 𝓝 (p₀, z₀), (∀ i, F i q.1 q.2 = 0) → z q.1 = q.2 := by sorry
