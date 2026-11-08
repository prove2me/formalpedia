-- Prove2me | Theorems.Thm_KhintchineTwoRegime_haagerup_inequality
-- name    : KhintchineTwoRegime.haagerup_inequality
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:35:09.119707+00:00
-- url     : https://prove2.me/theorems/48088b55-f4a6-4d8b-ad61-3e2801aefb64
-- title:
--   Haagerup's refined $L^1$-Khintchine estimate $K_n(\omega)\ge\sum_i\omega_i^2F(\omega_i^{-2})$
-- statement:
--   For every unit vector $\omega\in\mathbb R^n$, $\|\omega\|_2=1$,
--   $$
--   K_n(\omega)\ \ge\ \sum_{i=1}^n\omega_i^2\,F(\omega_i^{-2}),
--   $$
--   where $F$ is Haagerup's function (8), and a summand with $\omega_i=0$ is interpreted by continuity, i.e. as $0$ (since $F(s)\to\sqrt{2/\pi}$ as $s\to\infty$).
--
--   This is Haagerup's 1981 refinement of the $L^1$ Khintchine inequality, cited as eq. (9). It yields the bound $H$ of Lemma 2 and the case $a\le1/2$ of Corollary 1.
--
--   Differences from the source:
--   - encoding: a summand corresponding to ω_i = 0 is interpreted by continuity → the summand is 0 when ω i = 0 (if-then-else), and ω_i^{−2} is (ω_i²)⁻¹; reason: ω²F(ω^{−2}) → 0·√(2/π) = 0 as ω → 0; same values
--   - encoding: vectors ω ∈ ℝⁿ with the Euclidean norm ‖·‖₂, coordinates ω₁, …, ωₙ → Fin n → ℝ with the Euclidean norm √(∑ᵢ ωᵢ²) (the published HighDimProb.SparseRecovery.l2Norm), coordinates ω 0, …, ω (n−1); reason: Lean convention (Mathlib's ‖·‖ on Fin n → ℝ is the sup norm); same instances
--   - encoding: E over independent Rademacher signs → uniform average over all sign vectors Fin n → Bool (K); reason: the law of independent Rademacher signs is uniform on {−1, 1}ⁿ; same values
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), eq. (9), §2.2, p.6 (Haagerup [11])

import Mathlib
import Definitions.Def_KhintchineTwoRegime_K
import Definitions.Def_HighDimProb_SparseRecovery_L2Norm
import Definitions.Def_KhintchineTwoRegime_haagerupF
open HighDimProb.SparseRecovery (l2Norm)

namespace KhintchineTwoRegime

/-- Haagerup's refined `L¹`-Khintchine estimate (9) (cited in Fang–Wang, *A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions*, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), §2.2, p.6, from
Haagerup 1981): for every unit vector `ω`, `K_n(ω) ≥ ∑ᵢ ωᵢ² F(ωᵢ^{−2})`, where a summand with
`ωᵢ = 0` is interpreted by continuity.

**Formalization Note** As `s → ∞`, `F(s) → √(2/π)`, so `ωᵢ² F(ωᵢ^{−2}) → 0` as `ωᵢ → 0`;
the continuous extension of a summand at `ωᵢ = 0` is `0`, written with an `if`. `ωᵢ^{−2}`
is `(ωᵢ²)⁻¹`. -/
theorem haagerup_inequality (n : ℕ) (ω : Fin n → ℝ) (hω : l2Norm ω = 1) :
    ∑ i, (if ω i = 0 then 0 else ω i ^ 2 * haagerupF ((ω i ^ 2)⁻¹)) ≤ K n ω := by sorry

end KhintchineTwoRegime
