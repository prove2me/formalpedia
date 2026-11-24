-- Prove2me | Theorems.Thm_GlobalTheory_BorelAlg_Equivariant_isHomogeneous
-- name    : GlobalTheory.BorelAlg.Equivariant.isHomogeneous
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:01:40.862158+00:00
-- url     : https://prove2.me/theorems/3e35706a-2c98-46e0-9048-bdc65322ae32
-- title:
--   Equivariant: is Homogeneous
-- statement:
--   The Equivariant construction uses the is Homogeneous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsIsHomogeneousOfEquivariant.lean#L227-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsIsHomogeneousOfEquivariant.lean#L227-L265

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

theorem GlobalTheory.BorelAlg.Equivariant.isHomogeneous {a : ι × ℕ → ℕ} {Q : MvPolynomial (Lt m) L}
    (hf : Equivariant m L S a (algebraMap _ S Q)) :
    Q.IsHomogeneous (∑ τ, ∑ i : Fin (m τ), a (τ, (i : ℕ))) := by sorry
