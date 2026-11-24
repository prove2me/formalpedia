-- Prove2me | Theorems.Thm_GlobalTheory_csr_map_aeval
-- name    : GlobalTheory.csr_map_aeval
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:14:44.718261+00:00
-- url     : https://prove2.me/theorems/b28b8e9d-83ae-4d61-bcf9-b00ddb89638e
-- title:
--   Global Theory: csr map aeval
-- statement:
--   The Global Theory construction uses the csr map aeval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KerAevalOrthogonalRangeUnitarySelfReciprocal.lean#L12-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KerAevalOrthogonalRangeUnitarySelfReciprocal.lean#L12-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KerAevalOrthogonalRangeUnitarySelfReciprocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory

theorem GlobalTheory.csr_map_aeval {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (p : K[X]) :
    (aeval A p).map σ = aeval (A.map σ) (p.map σ) := by sorry
