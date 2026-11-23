-- Prove2me | Theorems.Thm_GlobalTheory_JR_NormalFormL_charpoly_companion_coeff
-- name    : GlobalTheory.JR.NormalFormL.charpoly_companion_coeff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:38:13.367433+00:00
-- url     : https://prove2.me/theorems/2b2275df-c951-41dd-b83d-31a5c8cadfd9
-- title:
--   Normal Form L: charpoly companion coeff
-- statement:
--   The Normal Form L construction uses the charpoly companion coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisBorderedMatrixNormalFormInvariants.lean#L58-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisBorderedMatrixNormalFormInvariants.lean#L58-L71

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

theorem GlobalTheory.JR.NormalFormL.charpoly_companion_coeff (p : Fin r → k) (i : Fin r) :
    (companion p).charpoly.coeff i = p i := by sorry
