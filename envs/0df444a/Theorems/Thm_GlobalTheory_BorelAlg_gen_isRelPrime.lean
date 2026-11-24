-- Prove2me | Theorems.Thm_GlobalTheory_BorelAlg_gen_isRelPrime
-- name    : GlobalTheory.BorelAlg.gen_isRelPrime
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:01:57.779014+00:00
-- url     : https://prove2.me/theorems/2f8b53a1-65a8-42ba-997e-68305e3136e3
-- title:
--   Borel Alg: gen is Rel Prime
-- statement:
--   The Borel Alg construction uses the gen is Rel Prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsIsHomogeneousOfEquivariant.lean#L74-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsIsHomogeneousOfEquivariant.lean#L74-L89

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

theorem GlobalTheory.BorelAlg.gen_isRelPrime {τ τ' : ι} (h : τ ≠ τ') :
    IsRelPrime (gen m L τ).det (gen m L τ').det := by sorry
