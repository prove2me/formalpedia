-- Prove2me | Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_parallel_assoc
-- name    : MiLAC.HybridCouplersPhaseShifters.parallel_assoc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:40:27.165097+00:00
-- url     : https://prove2.me/theorems/8297fd86-1707-438f-bf1b-e1a23d2b0583
-- title:
--   Hybrid Couplers Phase Shifters: parallel assoc
-- statement:
--   The parallel is associative, up to a relabelling of the ports.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/HybridCouplersPhaseShifters.lean#L121-L141
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/HybridCouplersPhaseShifters.lean#L121-L141

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Definitions.Def_LeanPool_MicrowaveNetworks_HybridCouplersPhaseShifters
set_option autoImplicit true
@[expose] public section
public section
open MiLAC MiLAC.HybridCouplersPhaseShifters

theorem MiLAC.HybridCouplersPhaseShifters.parallel_assoc {a b c : ℕ} (A : Network a) (B : Network b) (C : Network c) :
    NetEquiv ⟨a + b + c, parallel (parallel A B) C⟩
      ⟨a + (b + c), parallel A (parallel B C)⟩ := by sorry
