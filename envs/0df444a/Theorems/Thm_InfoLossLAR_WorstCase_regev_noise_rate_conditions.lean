-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_regev_noise_rate_conditions
-- name    : InfoLossLAR.WorstCase.regev_noise_rate_conditions
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T01:28:21.466302+00:00
-- url     : https://prove2.me/theorems/5b3988b0-fcd7-4536-b9c8-81fa2456c424
-- title:
--   The fixed Gaussian family satisfies Regev’s noise-rate conditions
-- statement:
--   For every integer security parameter λ ≥ 3, set α = σ(λ)/(√2 q(λ)) for the fixed family N(λ)=λ and σ(λ)=λ+2. Then 0 < α < 1 and 2√N(λ) < α q(λ). The √2 factor is part of the Gaussian convention. This proves only these exact numerical side conditions, without claiming the existence or polynomial time of a lattice reduction.
-- source:
--   Complete proof reused from Solutions/RegevBridgeLatticeInterfaces.lean, theorem InfoLossLAR.WorstCase.regev_noise_rate_conditions and its four local numerical helper proofs. It verifies the parameter conditions used in Regev, On lattices, learning with errors, random linear codes, and cryptography, May 2, 2009, Theorem 3.1; https://cims.nyu.edu/~regev/papers/qcrypto.pdf. No new mathematical argument is introduced.

import Definitions.Def_InfoLossLAR_WorstCase_Family

set_option autoImplicit false

namespace InfoLossLAR.WorstCase

theorem regev_noise_rate_conditions (lam : ℕ) (hlam : 3 ≤ lam) :
    let α : ℝ := (famσ lam : ℝ) / (Real.sqrt 2 * (famq lam : ℝ))
    0 < α ∧ α < 1 ∧ 2 * Real.sqrt (famN lam : ℝ) < α * (famq lam : ℝ) := by sorry

end InfoLossLAR.WorstCase
