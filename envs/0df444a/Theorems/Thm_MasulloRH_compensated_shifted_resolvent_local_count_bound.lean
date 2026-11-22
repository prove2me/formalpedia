-- Prove2me | Theorems.Thm_MasulloRH_compensated_shifted_resolvent_local_count_bound
-- name    : MasulloRH.compensated_shifted_resolvent_local_count_bound
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T23:41:08.929261+00:00
-- url     : https://prove2.me/theorems/2daf08e9-23f5-4e92-986b-dae65876b8cc
-- title:
--   A positive compensated shifted-resolvent kernel with uniform local counting bound
-- statement:
--   For every real height $T$, define the literal compensated resolvent kernel
--   $$
--   K_T(z)=\Re\left(\frac1{13/8+iT-z}-\frac1{5/2-z}\right)
--    +8\Re\left(\frac1{3-z}-\frac1{5/2-z}\right).
--   $$
--   For every $z=\beta+i\gamma$ satisfying $0\le\beta\le1$ and $\gamma^2\ge36$, the kernel dominates the positive Poisson kernel
--   $$
--   K_T(z)\ge\frac{13/8-\beta}{(13/8-\beta)^2+(T-\gamma)^2}>0.
--   $$
--   If $|\gamma-T|\le1$, then $K_T(z)\ge104/233$.
--
--   Consequently, for every finite family $(z_i)_{i<n}$ satisfying those strip and height conditions, every family of nonnegative real weights $(m_i)_{i<n}$, and every subset $S$ of indices lying in the radius-one window $[T-1,T+1]$ (of total height two),
--   $$
--   \sum_{i\in S}m_i\le\frac{233}{104}\sum_{i<n}m_iK_T(z_i).
--   $$
--   This includes the empty family, arbitrary real heights, and arbitrary nonnegative real multiplicity weights; it assumes neither conjugate pairing nor the Riemann Hypothesis. It is a finite algebraic counting ingredient. An application to actual zeta zeros additionally requires a justified infinite spectral identity and a rigorous arithmetic bound for the remaining kernel mass.
-- source:
--   New scalar-trace certificate construction for the Masullo RH mission. Pure real/complex algebra and finite sums over Mathlib. The explicit height-six strip hypotheses are motivated by the independently proved low-height zero-free rectangle. This theorem does not use that rectangle or any RH/Alpöge theorem as a formal dependency, and it does not close MasulloRH.regularized_trace_scalar_lower_bound.

import Mathlib
open scoped BigOperators

theorem MasulloRH.compensated_shifted_resolvent_local_count_bound (T : ℝ) :
    let K : ℂ → ℝ := fun z =>
      (((13/8 : ℂ) + (T : ℂ) * Complex.I - z)⁻¹ - ((5/2 : ℂ) - z)⁻¹).re +
        8 * (((3 : ℂ) - z)⁻¹ - ((5/2 : ℂ) - z)⁻¹).re
    (∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → 36 ≤ z.im^2 →
      (13/8-z.re) / ((13/8-z.re)^2+(T-z.im)^2) ≤ K z ∧
      0 < K z ∧ (|z.im-T| ≤ 1 → (104/233 : ℝ) ≤ K z)) ∧
    (∀ (n : ℕ) (z : Fin n → ℂ) (m : Fin n → ℝ) (S : Finset (Fin n)),
      (∀ i, 0 ≤ m i) → (∀ i, 0 ≤ (z i).re) → (∀ i, (z i).re ≤ 1) →
      (∀ i, 36 ≤ (z i).im^2) → (∀ i ∈ S, |(z i).im-T| ≤ 1) →
      (∑ i ∈ S, m i) ≤ (233/104 : ℝ) * ∑ i, m i * K (z i)) := by sorry
