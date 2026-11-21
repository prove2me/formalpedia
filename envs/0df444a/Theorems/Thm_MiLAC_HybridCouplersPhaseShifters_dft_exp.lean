-- Prove2me | Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_dft_exp
-- name    : MiLAC.HybridCouplersPhaseShifters.dft_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:41:13.839179+00:00
-- url     : https://prove2.me/theorems/5d010d93-07bd-47f3-b61b-67cc291741a9
-- title:
--   Hybrid Couplers Phase Shifters: dft exp
-- statement:
--   The exponential identity behind the radix-2 decomposition of the DFT.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/HybridCouplersPhaseShifters.lean#L619-L638
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/HybridCouplersPhaseShifters.lean#L619-L638

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Definitions.Def_LeanPool_MicrowaveNetworks_HybridCouplersPhaseShifters
set_option autoImplicit true
@[expose] public section
public section
open MiLAC MiLAC.HybridCouplersPhaseShifters

theorem MiLAC.HybridCouplersPhaseShifters.dft_exp (L a b i k : ℕ) :
    Complex.exp (-2 * Real.pi * Complex.I * ((i : ℂ) + 2 ^ L * a) * ((b : ℂ) + 2 * k) /
        2 ^ (L + 1)) =
      (-1) ^ (a * b) *
        Complex.exp (-2 * Real.pi * Complex.I * i * b / 2 ^ (L + 1)) *
        Complex.exp (-2 * Real.pi * Complex.I * i * k / 2 ^ L) := by sorry
