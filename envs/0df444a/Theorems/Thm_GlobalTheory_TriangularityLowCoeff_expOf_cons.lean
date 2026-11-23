-- Prove2me | Theorems.Thm_GlobalTheory_TriangularityLowCoeff_expOf_cons
-- name    : GlobalTheory.TriangularityLowCoeff.expOf_cons
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:37:39.670247+00:00
-- url     : https://prove2.me/theorems/f7430754-4345-482a-9d77-6b4672060c28
-- title:
--   Triangularity Low Coeff: exp Of cons
-- statement:
--   The Triangularity Low Coeff construction uses the exp Of cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoeffAnnihilatedOfAevalMemKerPow.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoeffAnnihilatedOfAevalMemKerPow.lean#L20-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoeffAnnihilatedOfAevalMemKerPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.TriangularityLowCoeff
open MvPolynomial

theorem GlobalTheory.TriangularityLowCoeff.expOf_cons {d : ℕ} (i : Fin d) (L : List (Fin d)) :
    expOf (i :: L) = Finsupp.single i 1 + expOf L := by sorry
