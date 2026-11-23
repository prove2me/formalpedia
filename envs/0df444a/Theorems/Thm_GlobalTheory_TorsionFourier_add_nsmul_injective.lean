-- Prove2me | Theorems.Thm_GlobalTheory_TorsionFourier_add_nsmul_injective
-- name    : GlobalTheory.TorsionFourier.add_nsmul_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:51:52.14281+00:00
-- url     : https://prove2.me/theorems/70040875-0366-4aa3-94b2-4b57d91b267e
-- title:
--   Torsion Fourier: add nsmul injective
-- statement:
--   The Torsion Fourier construction uses the add nsmul injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FourierExtractionTsumClass.lean#L103-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FourierExtractionTsumClass.lean#L103-L109

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
omit [Module.Finite ℤ X]

theorem GlobalTheory.TorsionFourier.add_nsmul_injective {N : ℕ} (hN : 0 < N) (α : X) :
    Function.Injective fun μ : X => α + N • μ := by sorry
