-- Prove2me | Theorems.Thm_LeeYangGap_SpectralGap_trace_ratio
-- name    : LeeYangGap.SpectralGap.trace_ratio
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:12:23.644628+00:00
-- url     : https://prove2.me/theorems/3780c5b8-d973-47fa-9955-82a72a3b8ead
-- title:
--   Lemma 14 — Trace-ratio bound
-- statement:
--   Let $P,Q$ be Hermitian operators on a nonzero finite-dimensional complex Hilbert space, with $P,Q\succeq bI$ for $b>0$ and $\|P-Q\|\le\eta$. Write $\delta=\eta/b$. For every integer $N\ge1$,
--   $$e^{-N\delta}\le(1+\delta)^{-N}\le\frac{\operatorname{Tr}P^N}{\operatorname{Tr}Q^N}\le(1+\delta)^N\le e^{N\delta}.$$
--   Here $\|\cdot\|$ is the Hilbert-space operator norm and $\eta\ge0$ follows from its bound. This is the full chain of inequalities, with positive real traces, for comparison of partition denominators.
--
--   Differences from the source:
--   - encoding: operators on a nonzero finite-dimensional Hilbert space → square complex matrices on a finite nonempty index type, with the L2 operator norm; reason: an orthonormal basis identifies exactly the same operators and preserves trace, positivity and norm
--   - encoding: Hermitian P,Q with P,Q≽bI and their trace ratio → P−bI and Q−bI positive semidefinite, and ratio of the real parts of their traces; reason: positive semidefiniteness includes Hermiticity, and these positive traces are real
-- source:
--   Chaithanya Rayudu, Jun Takahashi, Spectral gap of Lee-Yang Hamiltonians, STOC 2027 submission #575 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/575.pdf, Lemma 14, printed/PDF p. 19

import Mathlib
import Definitions.Def_LeeYangGap_SpectralGap_Analytic
open scoped BigOperators Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false
noncomputable section

namespace LeeYangGap.SpectralGap

/-- Rayudu–Takahashi, STOC 2027 submission #575; source index in items.yaml. -/
theorem trace_ratio {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P Q : Operator ι) (b η : ℝ) (hb : 0 < b)
    (hP : (P - (b : ℂ) • 1).PosSemidef)
    (hQ : (Q - (b : ℂ) • 1).PosSemidef) (hη : ‖P - Q‖ ≤ η)
    (N : ℕ) (hN : 1 ≤ N) :
    Real.exp (- (N : ℝ) * (η/b)) ≤ ((1 + η/b)^N)⁻¹ ∧
    ((1 + η/b)^N)⁻¹ ≤ (Matrix.trace (P^N)).re / (Matrix.trace (Q^N)).re ∧
    (Matrix.trace (P^N)).re / (Matrix.trace (Q^N)).re ≤ (1 + η/b)^N ∧
    (1 + η/b)^N ≤ Real.exp ((N : ℝ) * (η/b)) := by sorry
end LeeYangGap.SpectralGap
