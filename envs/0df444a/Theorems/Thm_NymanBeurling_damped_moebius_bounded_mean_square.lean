-- Prove2me | Theorems.Thm_NymanBeurling_damped_moebius_bounded_mean_square
-- name    : NymanBeurling.damped_moebius_bounded_mean_square
-- status  : Open
-- author  : @marozols
-- created : 2026-11-21T01:06:02.388462+00:00
-- url     : https://prove2.me/theorems/3e8f3057-501a-4494-bda8-f9facf580956
-- title:
--   A uniformly bounded subsequence of damped Möbius mean squares
-- statement:
--   Does there exist one finite B for which arbitrarily small positive ε admit arbitrarily large N such that every finite weighted square sum of the residual R(N,ε,m) is at most B? Here R(N,ε,m)=1+∑_{1≤d≤N} μ(d)d^{−ε}(m mod d)/d, with the natural weight 1/[m(m+1)]. The same B must work for all the chosen exponents, denominator cutoffs, and coordinate cutoffs.
--
--   This is an open unconditional assertion. Only one finite upper bound is required; the individual mean squares may stay separated from zero. Since the damped residuals already converge on each fixed coordinate prefix in the iterated limit, this bound suffices for weak Hilbert-space convergence along a diagonal. Orthogonal separation then puts the constant sequence in the norm-closed span of the remainders. Bagchi’s conditional norm convergence under RH implies this boundedness.
-- source:
--   B. Bagchi, On Nyman, Beurling and Baez-Duarte’s Hilbert space reformulation of the Riemann hypothesis, proof of Theorem 2 on pp. 140–141 and discrete Theorem 1, https://arxiv.org/pdf/math/0607733 . This weak boundedness reduction is a consequence of the discrete Hilbert-space formulation, not an unconditional assertion of that paper.

import Mathlib

open Filter Topology Finset

theorem NymanBeurling.damped_moebius_bounded_mean_square :
    ∃ B : ℝ, ∃ᶠ ε : ℝ in 𝓝[>] 0, ∃ᶠ N : ℕ in atTop, ∀ H : ℕ,
      ∑ n ∈ Finset.range H, (1 + ∑ d ∈ Finset.Ioc 0 N,
        ((ArithmeticFunction.moebius d : ℝ)/(d:ℝ)^ε)*(((n+1)%d:ℕ):ℝ)/(d:ℝ))^2 /
        ((n+1:ℝ)*(n+2:ℝ)) ≤ B := by sorry
