-- Prove2me | Theorems.Thm_GRH_primitive_nonprincipal_LFunction_nonzero_below_record
-- name    : GRH.primitive_nonprincipal_LFunction_nonzero_below_record
-- status  : Open
-- author  : @scuba8684
-- created : 2026-11-26T13:04:29.097785+00:00
-- url     : https://prove2.me/theorems/046910d8-f152-46b2-aff5-b1c00405bcd0
-- title:
--   Zero exclusion for primitive nonprincipal Dirichlet L-functions in the remaining strip
-- statement:
--   For every positive conductor $d$ and every primitive nonprincipal complex Dirichlet character $\psi$ modulo $d$, $L(s,\psi)$ is nonzero throughout $1/2<\Re(s)\le0.8749570698$. This is the open analytic input for the centered Möbius residue-bias argument. The upper endpoint is included and all imaginary parts are quantified.
-- source:
--   Derived in the centered Möbius bilinear problem https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 and the square-cutoff residue-bias reduction https://prove2.me/theorems/ebfcf6de-c11b-4420-bb99-92e3875c1325.

import Mathlib.NumberTheory.LSeries.DirichletContinuation

theorem GRH.primitive_nonprincipal_LFunction_nonzero_below_record
    (d : ℕ) [NeZero d] (ψ : DirichletCharacter ℂ d) (hprim : ψ.IsPrimitive) (hψ : ψ ≠ 1)
    (s : ℂ) (hl : (1/2:ℝ) < s.re) (hr : s.re ≤ (0.8749570698:ℝ)) :
    ψ.LFunction s ≠ 0 := by sorry
