-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_FrameCoefficientData_isInnerLattice_std
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.FrameCoefficientData.isInnerLattice_std
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:09:47.806729+00:00
-- url     : https://prove2.me/theorems/1a607110-fc78-4e3e-8b27-5919ee0b8f0b
-- title:
--   Frame Coefficient Data: is Inner Lattice std
-- statement:
--   The Frame Coefficient Data construction uses the is Inner Lattice std property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/SiegelWeilLocal/FrameCoefficientData.lean#L380-L408
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/SiegelWeilLocal/FrameCoefficientData.lean#L380-L408

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelWeilLocal_FrameCoefficientData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ENNReal
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.FrameCoefficientData
variable {o F E V : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o]
  [Field F] [Algebra o F] [IsFractionRing o F]
  [CommRing E] [StarRing E] [Algebra F E] [Algebra o E]
  [AddCommGroup V] [Module E V] {r : ℕ}

theorem GlobalTheory.IndefiniteRowSideFullHecke.FrameCoefficientData.isInnerLattice_std (n : ℕ) (A : Frame F (Fin n → E) 0) (i₀ : Fin n)
    (hz : ∀ i, A.z i ∈ MaxOrd o E) (h1 : A.z i₀ = 1)
    (hs : ∀ x ∈ MaxOrd o E, star x ∈ MaxOrd o E) :
    A.IsInnerLattice (negStd E n)
      (Submodule.span (MaxOrd o E) (Set.range fun i : Fin n => (Pi.single i 1 : Fin n → E))) := by sorry
