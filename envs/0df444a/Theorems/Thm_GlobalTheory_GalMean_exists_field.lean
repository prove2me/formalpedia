-- Prove2me | Theorems.Thm_GlobalTheory_GalMean_exists_field
-- name    : GlobalTheory.GalMean.exists_field
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:13:42.056675+00:00
-- url     : https://prove2.me/theorems/434fa7ab-2307-4123-aa5d-38b18922ddd9
-- title:
--   Gal Mean: exists field
-- statement:
--   The Gal Mean construction uses the exists field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeanLogNormConjugatesOverIdealClasses.lean#L10-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeanLogNormConjugatesOverIdealClasses.lean#L10-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_LatticeNormTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeanLogNormConjugatesOverIdealClasses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.GalMean
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport

theorem GlobalTheory.GalMean.exists_field {K : Type} [Field K] [NumberField K] (φK : K →+* ℂ) (a b : ℂ)
    (ha : IsAlgebraic ℚ a) (hb : IsAlgebraic ℚ b) :
    ∃ L : IntermediateField ℚ ℂ, FiniteDimensional ℚ L ∧ IsGalois ℚ L ∧ (∀ x : K, φK x ∈ L) ∧ a ∈ L ∧ b ∈ L := by sorry
