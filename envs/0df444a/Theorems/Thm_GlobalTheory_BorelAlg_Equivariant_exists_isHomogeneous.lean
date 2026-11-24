-- Prove2me | Theorems.Thm_GlobalTheory_BorelAlg_Equivariant_exists_isHomogeneous
-- name    : GlobalTheory.BorelAlg.Equivariant.exists_isHomogeneous
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:02:10.81641+00:00
-- url     : https://prove2.me/theorems/f1d10cd5-4b56-4ed4-9a1b-ac7bb91f6cd6
-- title:
--   Equivariant: exists is Homogeneous
-- statement:
--   The Equivariant construction uses the exists is Homogeneous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsIsHomogeneousOfEquivariant.lean#L267-L282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsIsHomogeneousOfEquivariant.lean#L267-L282

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

theorem GlobalTheory.BorelAlg.Equivariant.exists_isHomogeneous {a : ι × ℕ → ℕ} {f : S} (hf : Equivariant m L S a f) :
    ∃ P : MvPolynomial (Lt m) L, algebraMap _ S P = f ∧
      P.IsHomogeneous (∑ τ, ∑ i : Fin (m τ), a (τ, (i : ℕ))) := by sorry
