-- Prove2me | Theorems.Thm_LamLitt_omega_integrality_iff_first_coeffs
-- name    : LamLitt.omega_integrality_iff_first_coeffs
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-21T23:25:44.800462+00:00
-- url     : https://prove2.me/theorems/7161814b-92e5-4416-94d8-88b9c0504c2e
-- title:
--   Condition (3) without $\omega$: the first $mp$ coefficients are $p$-integral for large $p$
-- statement:
--   Let $(a_k)_{k\ge 0}$ be a sequence of rational numbers. The following are equivalent.
--
--   1. ($\omega(p)$-integrality.) There is a function $\omega$ from the set of primes to $\mathbb{Z}$ with $\lim_{p\to\infty}\omega(p)/p=\infty$ such that, for every prime $p$, the numbers $a_0,a_1,\dots,a_{\omega(p)}$ lie in $\mathbb{Z}_{(p)}$, the ring of rational numbers whose denominators are prime to $p$.
--   2. For every integer $m\ge 0$ there is $P_0$ such that for every prime $p\ge P_0$ the first $mp$ terms $a_0,a_1,\dots,a_{mp-1}$ lie in $\mathbb{Z}_{(p)}$:
--
--   $$\forall m\ \ \exists P_0\ \ \forall p\ge P_0\text{ prime}\ \ \forall k<mp:\quad a_k\in\mathbb{Z}_{(p)}.$$
--
--   Statement 1 is condition (3) of the Lam–Litt conjecture, applied to the Taylor coefficients of a power series. Statement 2 is the description of that condition given by Lam and Litt immediately after the conjecture. It eliminates the auxiliary function $\omega$ and the limit, which makes condition (3) easier to verify in examples and easier to use as a hypothesis.
--
--   **Formalization Note** Statement 1 uses the mission's definitions `omegaSuperlinear` and `omegaIntegral`; negative values of $\omega$ impose no condition. In statement 2, $m$ ranges over all natural numbers (the case $m=0$ is vacuous), and membership in $\mathbb{Z}_{(p)}$ is expressed as: the reduced denominator of $a_k$ is coprime to $p$.
-- source:
--   Y. H. J. Lam, D. Litt, Algebraicity and integrality of solutions to differential equations, https://arxiv.org/abs/2501.13175 (v1), p. 3, the paragraph following Conjecture 1.1.1: 'condition (3), which is a priori weaker, only asserts that for all m > 0 and sufficiently large p (in terms of m), the first mp coefficients of the Taylor expansion of f have denominators which are prime to p.' The equivalence with the formal condition (3) (existence of omega with omega(p)/p -> infinity) is implicit there.

import Definitions.Def_LamLitt_Defs
import Mathlib

open PowerSeries

namespace LamLitt

theorem omega_integrality_iff_first_coeffs (a : ℕ → ℚ) :
    (∃ ω : Nat.Primes → ℤ, omegaSuperlinear ω ∧ omegaIntegral ω a) ↔
      ∀ m : ℕ, ∃ P₀ : ℕ, ∀ p : Nat.Primes, P₀ ≤ (p : ℕ) →
        ∀ k : ℕ, k < m * (p : ℕ) → Nat.Coprime (a k).den p := by sorry

end LamLitt
