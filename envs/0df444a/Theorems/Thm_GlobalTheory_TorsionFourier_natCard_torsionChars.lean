-- Prove2me | Theorems.Thm_GlobalTheory_TorsionFourier_natCard_torsionChars
-- name    : GlobalTheory.TorsionFourier.natCard_torsionChars
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:11:30.200449+00:00
-- url     : https://prove2.me/theorems/25cca459-d0c9-4f3a-8dd9-a3b055bcb94b
-- title:
--   Torsion Fourier: nat Card torsion Chars
-- statement:
--   The Torsion Fourier construction uses the nat Card torsion Chars property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FourierExtractionTsumClass.lean#L91-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FourierExtractionTsumClass.lean#L91-L97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FourierExtractionTsumClass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
open GlobalTheory.TorsionFourier
variable {K X : Type} [Field K] [AddCommGroup X]
variable [Module.Free ℤ X] [Module.Finite ℤ X]
open Module
variable {K X : Type} [Field K] [AddCommGroup X]
variable [Module.Free ℤ X] [Module.Finite ℤ X]

theorem GlobalTheory.TorsionFourier.natCard_torsionChars {N : ℕ} {ζ : K} (hN : 0 < N)
    (hζ : IsPrimitiveRoot ζ N) :
    Nat.card (_root_.GlobalTheory.TorsionFourier.torsionChars K X N) = N ^ finrank ℤ X := by sorry
