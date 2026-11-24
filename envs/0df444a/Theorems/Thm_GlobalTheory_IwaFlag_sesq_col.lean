-- Prove2me | Theorems.Thm_GlobalTheory_IwaFlag_sesq_col
-- name    : GlobalTheory.IwaFlag.sesq_col
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:22:25.574475+00:00
-- url     : https://prove2.me/theorems/ae3415cf-c1c4-4cb7-a692-1cb6659440bd
-- title:
--   Iwa Flag: sesq col
-- statement:
--   The Iwa Flag construction uses the sesq col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsFlagDualMatrix.lean#L182-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsFlagDualMatrix.lean#L182-L184

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsFlagDualMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IwaFlag
variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {ρ : ℕ} {c : R →+* R} {ε : R} {O : AddSubgroup R}
  {h : V →ₗ[R] V →ₛₗ[c] R} {M : AddSubgroup V}
open Matrix

theorem GlobalTheory.IwaFlag.sesq_col {n p q : ℕ} (G : Matrix (Fin n) (Fin n) R) (A : Matrix (Fin n) (Fin p) R) (B : Matrix (Fin n) (Fin q) R)
    (i : Fin p) (j : Fin q) : sesq c G (fun k => A k i) (fun k => B k j) = ((B.map c)ᵀ * (G * A)) j i := by sorry
