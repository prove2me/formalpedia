-- Prove2me | Theorems.Thm_GlobalTheory_BorelAlg_inj_block
-- name    : GlobalTheory.BorelAlg.inj_block
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:57.332844+00:00
-- url     : https://prove2.me/theorems/ba67162d-7bcd-4ac1-98fa-a5c12bef0129
-- title:
--   Borel Alg: inj block
-- statement:
--   The Borel Alg construction uses the inj block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsIsHomogeneousOfEquivariant.lean#L56-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsIsHomogeneousOfEquivariant.lean#L56-L58

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

theorem GlobalTheory.BorelAlg.inj_block (τ : ι) :
    Function.Injective (fun p : Fin (m τ) × Fin (m τ) => (⟨τ, p⟩ : Lt m)) := by sorry
