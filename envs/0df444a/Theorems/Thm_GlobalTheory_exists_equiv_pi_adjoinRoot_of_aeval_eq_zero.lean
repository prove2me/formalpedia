-- Prove2me | Theorems.Thm_GlobalTheory_exists_equiv_pi_adjoinRoot_of_aeval_eq_zero
-- name    : GlobalTheory.exists_equiv_pi_adjoinRoot_of_aeval_eq_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:31:32.911524+00:00
-- url     : https://prove2.me/theorems/1871a299-65ee-4176-a8f9-6f38ddcc1f7c
-- title:
--   Global Theory: exists equiv pi adjoin Root of aeval eq zero
-- statement:
--   The Global Theory construction uses the exists equiv pi adjoin Root of aeval eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSurjectivePiAdjoinRootKerEqRange.lean#L6-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSurjectivePiAdjoinRootKerEqRange.lean#L6-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSurjectivePiAdjoinRootKerEqRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory

theorem GlobalTheory.exists_equiv_pi_adjoinRoot_of_aeval_eq_zero (F : Type) [Field F] (Q : Type) [AddCommGroup Q]
    [Module F Q] [FiniteDimensional F Q] (g : Module.End F Q) (f : F[X]) [Fact (Irreducible f)]
    (h : aeval g f = 0) :
    ∃ (t : ℕ) (e : Q ≃ₗ[F] (Fin t → AdjoinRoot f)),
      (∀ v, e (g v) = AdjoinRoot.root f • e v) ∧ Module.finrank F Q = f.natDegree * t := by sorry
