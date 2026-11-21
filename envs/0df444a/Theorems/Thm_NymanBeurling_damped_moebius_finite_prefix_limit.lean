-- Prove2me | Theorems.Thm_NymanBeurling_damped_moebius_finite_prefix_limit
-- name    : NymanBeurling.damped_moebius_finite_prefix_limit
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T01:01:35.509716+00:00
-- url     : https://prove2.me/theorems/c7dae3e6-08fd-4a3e-b304-dc3dc18c3f7c
-- title:
--   Unconditional convergence of damped Möbius remainders on each finite coordinate prefix
-- statement:
--   For every positive accuracy δ and every finite coordinate cutoff M, all sufficiently small positive exponents ε have the following property. Once N is sufficiently large (depending on ε, M and δ), the damped Möbius residual has absolute value below δ at every integer 1≤m≤M:
--   R(N,ε,m)=1+∑_{1≤d≤N} μ(d)d^{−ε}(m mod d)/d.
--   No zero-free assertion inside the critical strip is used. The quantifiers control one prescribed finite prefix. Uniform boundedness or convergence for the infinite weighted square norm is a further issue.
-- source:
--   B. Bagchi, On Nyman, Beurling and Baez-Duarte’s Hilbert space reformulation of the Riemann hypothesis, proof of Theorem 2 and the sequence form of Theorem 1, https://arxiv.org/pdf/math/0607733 . The finite-prefix statement here is an unconditional consequence of the absolutely convergent Möbius series to the right of 1 and elementary Möbius inversion.

import Mathlib

open Filter Topology

theorem NymanBeurling.damped_moebius_finite_prefix_limit (M : ℕ) (δ : ℝ) (hδ : 0<δ) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ᶠ N : ℕ in atTop, ∀ m ∈ Finset.Ioc 0 M,
      |1 + ∑ d ∈ Finset.Ioc 0 N, ((ArithmeticFunction.moebius d : ℝ)/(d:ℝ)^ε) * ((m%d:ℕ):ℝ)/(d:ℝ)| < δ := by sorry
