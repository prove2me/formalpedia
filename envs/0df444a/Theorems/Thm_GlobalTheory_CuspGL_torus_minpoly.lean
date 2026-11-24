-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_torus_minpoly
-- name    : GlobalTheory.CuspGL.torus_minpoly
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:33:05.497796+00:00
-- url     : https://prove2.me/theorems/8dc6859c-db45-4332-8d60-f28d09d9a4bc
-- title:
--   Cusp GL: torus minpoly
-- statement:
--   The Cusp GL construction uses the torus minpoly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FrobeniusTorusMinpolyDegreeRootPowerSum.lean#L90-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FrobeniusTorusMinpolyDegreeRootPowerSum.lean#L90-L124

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FrobeniusTorusMinpolyDegreeRootPowerSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL
variable {F : Type} [Field F] [Finite F]
open Polynomial
variable {F : Type} [Field F] [Finite F]

theorem GlobalTheory.CuspGL.torus_minpoly : ∀ (F : Type) [Field F] [Finite F]
    (θ : AlgebraicClosure F →* ℂ) (n : ℕ), 0 < n →
    ∀ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1},
      (minpoly F α).natDegree ∣ n ∧ (minpoly F α).coeff 0 ≠ 0 ∧
        ∀ k : ℕ, _root_.GlobalTheory.CuspGL.rootSum θ k
            (minpoly F α ^ (n / (minpoly F α).natDegree)) =
          ∑ i ∈ Finset.range n, θ (α ^ Nat.card F ^ i) ^ k := by sorry
