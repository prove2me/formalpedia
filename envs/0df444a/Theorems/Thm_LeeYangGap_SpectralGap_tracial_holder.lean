-- Prove2me | Theorems.Thm_LeeYangGap_SpectralGap_tracial_holder
-- name    : LeeYangGap.SpectralGap.tracial_holder
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:12:35.94756+00:00
-- url     : https://prove2.me/theorems/78ded717-c81c-4cb4-b973-add26cb1819b
-- title:
--   Fact 15 — Tracial matrix Hölder inequality
-- statement:
--   Let $A_i$ be arbitrary operators and $B_i$ Hermitian positive semidefinite operators on a finite-dimensional complex Hilbert space, for a finite list of indices $i$. Let $b_i\ge0$ be real with $N=\sum_i b_i>0$, and set $\|B\|_N=(\operatorname{Tr}B^N)^{1/N}$ using spectral real powers. Then
--   $$\left|\operatorname{Tr}\prod_i A_iB_i^{b_i}\right|\le\prod_i\|A_i\|\prod_i\|B_i\|_N^{b_i}.$$
--   Products inside the trace retain list order. The norms of $A_i$ are Hilbert-space operator norms. Singular $B_i$, zero exponents, the zero-dimensional Hilbert space and every real $N>0$ are included. Identity factors permit arbitrary finite interleavings. This trace estimate is the general finite-dimensional analytic input for the moment bounds.
--
--   Differences from the source:
--   - encoding: operators on a finite-dimensional Hilbert space → square complex matrices on a finite index type, with the L2 operator norm; reason: an orthonormal basis identifies exactly the same operators and preserves trace, positivity and norm
--   - encoding: real powers of PSD matrices and their Schatten trace quantities → continuous spectral functional calculus with Real.rpow, including 0^0=1; reason: matches spectral powers including singular matrices and zero exponents; total degree remains arbitrary positive real
-- source:
--   Chaithanya Rayudu, Jun Takahashi, Spectral gap of Lee-Yang Hamiltonians, STOC 2027 submission #575 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/575.pdf, Fact 15, printed/PDF p. 19

import Mathlib
import Definitions.Def_LeeYangGap_SpectralGap_Analytic
open scoped BigOperators Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false
noncomputable section

namespace LeeYangGap.SpectralGap

/-- Rayudu–Takahashi, STOC 2027 submission #575; source index in items.yaml. -/
theorem tracial_holder {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ℕ) (A B : Fin r → Operator ι) (b : Fin r → ℝ)
    (hB : ∀ i, (B i).PosSemidef) (hb : ∀ i, 0 ≤ b i)
    (hN : 0 < ∑ i, b i) :
    ‖Matrix.trace ((List.ofFn (fun i : Fin r => A i * realPower (B i) (b i))).prod)‖ ≤
      (∏ i, ‖A i‖) * ∏ i, (schattenPSD (B i) (∑ j, b j)) ^ (b i) := by sorry
end LeeYangGap.SpectralGap
