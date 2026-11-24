-- Prove2me | Theorems.Thm_GlobalTheory_SatakeWeyl_ContractProof_mat_inv_diag
-- name    : GlobalTheory.SatakeWeyl.ContractProof.mat_inv_diag
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:28:25.5118+00:00
-- url     : https://prove2.me/theorems/47fa10b1-230c-40f1-b992-e328b871e663
-- title:
--   Contract Proof: mat inv diag
-- statement:
--   The Contract Proof construction uses the mat inv diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryDominantDiagonalConjugationContracts.lean#L13-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryDominantDiagonalConjugationContracts.lean#L13-L22

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryDominantDiagonalConjugationContracts
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
noncomputable section
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.ContractProof
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {r : ℕ}
omit [Valued L (WithZero (Multiplicative ℤ))]

theorem GlobalTheory.SatakeWeyl.ContractProof.mat_inv_diag {ϖ : L} (h0 : ϖ ≠ 0) (c : Fin r → ℤ) (s : GU σ r)
    (hs : mat s = Matrix.diagonal (fun i => ϖ ^ c i)) :
    mat s⁻¹ = Matrix.diagonal (fun i => ϖ ^ (-c i)) := by sorry
