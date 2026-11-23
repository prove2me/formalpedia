-- Prove2me | Theorems.Thm_GlobalTheory_BorelAlg_gen_det_ne_zero
-- name    : GlobalTheory.BorelAlg.gen_det_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:03:20.719876+00:00
-- url     : https://prove2.me/theorems/7e864f0d-5f30-4285-a073-cb41be6b2ffe
-- title:
--   Borel Alg: gen det ne zero
-- statement:
--   The Borel Alg construction uses the gen det ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsIsHomogeneousOfEquivariant.lean#L68-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsIsHomogeneousOfEquivariant.lean#L68-L72

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

theorem GlobalTheory.BorelAlg.gen_det_ne_zero (τ : ι) : (gen m L τ).det ≠ 0 := by sorry
