-- Prove2me | Theorems.Thm_GlobalTheory_SatakeWeyl_ContractProof_mat_pow_diag
-- name    : GlobalTheory.SatakeWeyl.ContractProof.mat_pow_diag
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:47:23.364854+00:00
-- url     : https://prove2.me/theorems/176df1ed-5ea1-4527-bd75-677b417282a3
-- title:
--   Contract Proof: mat pow diag
-- statement:
--   The Contract Proof construction uses the mat pow diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryDominantDiagonalConjugationContracts.lean#L33-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryDominantDiagonalConjugationContracts.lean#L33-L42

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

theorem GlobalTheory.SatakeWeyl.ContractProof.mat_pow_diag {ϖ : L} (h0 : ϖ ≠ 0) (c : Fin r → ℤ) (s : GU σ r)
    (hs : mat s = Matrix.diagonal (fun i => ϖ ^ c i)) (j : ℕ) :
    mat (s ^ j) = Matrix.diagonal (fun i => ϖ ^ ((j : ℤ) * c i)) := by sorry
