-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_inverseUnipotentVolume_conj_diagonal_eq
-- name    : GlobalTheory.T.exists_inverseUnipotentVolume_conj_diagonal_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:30:56.485347+00:00
-- url     : https://prove2.me/theorems/448dc27a-5813-5ee1-a38a-81ca0193b18a
-- title:
--   T: exists inverse Unipotent Volume conj diagonal eq
-- statement:
--   The T construction uses the exists inverse Unipotent Volume conj diagonal eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsInverseUnipotentVolumeConjDiagonalEqStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsInverseUnipotentVolumeConjDiagonalEqStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInverseUnipotentVolumeConjDiagonalEq
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInverseUnipotentVolumeConjDiagonalEqStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_inverseUnipotentVolume_conj_diagonal_eq : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (ϖ : kˣ), IsUnif ϖ → ∀ t : n ⊕ Fin c, ∃ z : ℤ, invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL (Pi.mulSingle t ϖ))).toMonoidHom) = (resCard k : ℚ) ^ z ∧ |z| ≤ Fintype.card (n ⊕ Fin c) := by sorry
