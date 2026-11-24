-- Prove2me | Theorems.Thm_GlobalTheory_BorelAlg_Equivariant_det_pow_dvd
-- name    : GlobalTheory.BorelAlg.Equivariant.det_pow_dvd
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:01:24.854169+00:00
-- url     : https://prove2.me/theorems/4bfaf9f5-96b8-45a5-8bf5-c4c8b0d2561e
-- title:
--   Equivariant: det pow dvd
-- statement:
--   The Equivariant construction uses the det pow dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsIsHomogeneousOfEquivariant.lean#L138-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsIsHomogeneousOfEquivariant.lean#L138-L225

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IrreducibleDetOfIsRelPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsIsHomogeneousOfEquivariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.BorelAlg
variable {ι : Type} (m : ι → ℕ) (L : Type) [Field L]
variable [Fintype ι]
variable {m L} {S : Type} [CommRing S] [Algebra (MvPolynomial (Lt m) L) S]
  [IsLocalization.Away (∏ τ, (gen m L τ).det) S]

theorem GlobalTheory.BorelAlg.Equivariant.det_pow_dvd {a : ι × ℕ → ℕ} {f : S} (hf : Equivariant m L S a f)
    {P : MvPolynomial (Lt m) L} {N : ℕ}
    (hP : f * algebraMap _ S ((∏ τ, (gen m L τ).det) ^ N) = algebraMap _ S P) (τ₀ : ι) :
    (gen m L τ₀).det ^ N ∣ P := by sorry
