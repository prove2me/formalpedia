-- Prove2me | Theorems.Thm_GlobalTheory_DeformedSum_Series_series_differentiable
-- name    : GlobalTheory.DeformedSum.Series.series_differentiable
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:36:10.706078+00:00
-- url     : https://prove2.me/theorems/1030bf4e-fc0b-4125-ac82-ce207ef5ddf1
-- title:
--   Series: series differentiable
-- statement:
--   The Series construction uses the series differentiable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SeriesDifferentiable.lean#L10-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SeriesDifferentiable.lean#L10-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemIntegersOfMemHatO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DeformedProductDerivativeTermNormLeUniformStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasFDerivAtDeformedProductDerivativeTermStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SeriesDifferentiable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum
open GlobalTheory GlobalTheory.DeformedSum GlobalTheory.DeformedSum.Series

theorem GlobalTheory.DeformedSum.Series.series_differentiable : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ), IsCMType φ → ∀ s : ℕ, 2 ≤ s → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ → ∀ (m : I → ℕ) (z : I → ℂ), z ∈ polydisc I → Summable (fun q : modUnits (lattice c y) => dTerm φ (2 * s) m z q.1.out) ∧ DifferentiableAt ℂ (fun w : I → ℂ => ∑' q : modUnits (lattice c y), dTerm φ (2 * s) m w q.1.out) z ∧ ∀ i : I, HasLineDerivAt ℂ (fun w : I → ℂ => ∑' q : modUnits (lattice c y), dTerm φ (2 * s) m w q.1.out) (∑' q : modUnits (lattice c y), dTerm φ (2 * s) (m + Pi.single i 1) z q.1.out) z (Pi.single i 1) := by sorry
