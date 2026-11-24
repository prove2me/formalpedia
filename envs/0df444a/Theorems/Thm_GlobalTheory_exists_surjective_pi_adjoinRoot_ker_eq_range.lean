-- Prove2me | Theorems.Thm_GlobalTheory_exists_surjective_pi_adjoinRoot_ker_eq_range
-- name    : GlobalTheory.exists_surjective_pi_adjoinRoot_ker_eq_range
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:42:29.135548+00:00
-- url     : https://prove2.me/theorems/8194131c-1cc2-4b02-bedf-8b46b659486c
-- title:
--   Global Theory: exists surjective pi adjoin Root ker eq range
-- statement:
--   The Global Theory construction uses the exists surjective pi adjoin Root ker eq range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSurjectivePiAdjoinRootKerEqRange.lean#L34-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSurjectivePiAdjoinRootKerEqRange.lean#L34-L75

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

theorem GlobalTheory.exists_surjective_pi_adjoinRoot_ker_eq_range (F : Type) [Field F] (V : Type)
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] (g : Module.End F V) (f : F[X])
    [Fact (Irreducible f)] :
    ∃ (t : ℕ) (π : V →ₗ[F] (Fin t → AdjoinRoot f)), Function.Surjective π ∧
      (∀ v, π (g v) = AdjoinRoot.root f • π v) ∧
      LinearMap.ker π = LinearMap.range (aeval g f) ∧
      Module.finrank F (LinearMap.ker (aeval g f)) = f.natDegree * t := by sorry
