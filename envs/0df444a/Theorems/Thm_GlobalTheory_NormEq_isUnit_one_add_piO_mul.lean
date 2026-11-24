-- Prove2me | Theorems.Thm_GlobalTheory_NormEq_isUnit_one_add_piO_mul
-- name    : GlobalTheory.NormEq.isUnit_one_add_piO_mul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:34:15.649543+00:00
-- url     : https://prove2.me/theorems/248bbe3c-cc2e-4ba3-9596-f5da6aa632a0
-- title:
--   Norm Eq: is Unit one add pi O mul
-- statement:
--   The Norm Eq construction uses the is Unit one add pi O mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsUnitOneAddPiOMul.lean#L104-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsUnitOneAddPiOMul.lean#L104-L116

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOneAddPiOMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Formalism.UG
open GlobalTheory GlobalTheory.NormEq
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem GlobalTheory.NormEq.isUnit_one_add_piO_mul {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q)
    (P : GlobalTheory.UTr.Csr (sigO σ h.2.1)) (a : GlobalTheory.UTr.Alg P) :
    IsUnit (1 + algebraMap (intL L) (GlobalTheory.UTr.Alg P) (piO h) * a) := by sorry
