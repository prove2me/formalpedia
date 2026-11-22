-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_uniform_rectangular_gaussian_preparation
-- name    : InfoLossLAR.WorstCase.RegevSearch.uniform_rectangular_gaussian_preparation
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T05:54:51.80854+00:00
-- url     : https://prove2.me/theorems/912efb88-48a6-4e10-b841-1070dd0ad365
-- title:
--   Uniform circuit preparation of the framed fine-lattice Gaussian state
-- statement:
--   There exist two polynomial-time functions which compute the register sizes and emit a finite-gate preparation circuit for every encoded nonsingular integer basis, admissible Gaussian width and valid old sample pool. For every output register whose capacity exceeds the requested stage word, the emitted circuit starts at the all-zero state and prepares the normalized finite Gaussian on the fine dual lattice, with the prescribed Hilbert-space norm error and a unit spectator state. The descriptor also bounds the size of each framed quotient word, all decoder inputs and all answers.
-- source:
--   Source preparation for the Fourier row of https://prove2.me/theorems/23174e03-6b1d-4113-b6b9-4dab17fa850a

import Definitions.Def_InfoLossLAR_ReciprocallyScaledGaussianSource
set_option autoImplicit false
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RectangularSource
open InfoLossLAR.WorstCase.ControlledNativeCode OAI.MetricKMedian.Binary.Automatic

theorem InfoLossLAR.WorstCase.RegevSearch.uniform_rectangular_gaussian_preparation :
    ∃ describe : Cell.Input → RawFront.Spec, Poly describe ∧
    ∃ emit : Cell.Input × List Unit → List GateCode, Poly emit ∧ RawFront.frontContract describe emit := by sorry
