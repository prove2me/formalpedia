-- Prove2me | Theorems.Thm_GlobalTheory_NormEq_piO_mem_of_isMaximal
-- name    : GlobalTheory.NormEq.piO_mem_of_isMaximal
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:34:30.660697+00:00
-- url     : https://prove2.me/theorems/80575a00-0594-4206-ba5a-b1a891826d48
-- title:
--   Norm Eq: pi O mem of is Maximal
-- statement:
--   The Norm Eq construction uses the pi O mem of is Maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsUnitOneAddPiOMul.lean#L78-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsUnitOneAddPiOMul.lean#L78-L102

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

theorem GlobalTheory.NormEq.piO_mem_of_isMaximal {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) {M : Ideal (intL L)}
    (hM : M.IsMaximal) : piO h ∈ M := by sorry
