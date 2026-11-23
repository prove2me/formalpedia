-- Prove2me | Theorems.Thm_GlobalTheory_JR_NormalFormL_companion_pow_ev
-- name    : GlobalTheory.JR.NormalFormL.companion_pow_ev
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:38:26.948786+00:00
-- url     : https://prove2.me/theorems/ebac6607-0031-4ff7-b893-bd3259c299e7
-- title:
--   Normal Form L: companion pow ev
-- statement:
--   The Normal Form L construction uses the companion pow ev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisBorderedMatrixNormalFormInvariants.lean#L47-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisBorderedMatrixNormalFormInvariants.lean#L47-L51

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariants
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.NormalFormL
variable {k : Type} [Field k] {r : ℕ}

theorem GlobalTheory.JR.NormalFormL.companion_pow_ev (p : Fin r → k) (i : ℕ) (hi : i < r) :
    companion p ^ i *ᵥ ev r k 0 = ev r k i := by sorry
