-- Prove2me | Theorems.Thm_HankelIrrationality_decay_of_normalized_family
-- name    : HankelIrrationality.decay_of_normalized_family
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-04T13:58:08.582546+00:00
-- url     : https://prove2.me/theorems/223b1f61-8bae-4254-83b4-3815a8a23abb
-- title:
--   Normalization growth below real decay gives integer polynomials with $e^{-cn^2}$ values
-- statement:
--   Let $F_n\in\mathbb Q[X]$ and $m_n>0$ with $m_nF_n\in\mathbb Z[X]$ eventually. Suppose, for every $\varepsilon>0$ and all large $n$,
--   $$\log m_n\le(A+\varepsilon)(\kappa n)^2,\qquad 0<F_n(\xi),\quad \log F_n(\xi)\le(U+\varepsilon)(\kappa n)^2,$$
--   with $\kappa>0$ and $A+U<0$. Then for some $c>0$ and all large $n$, $Q_n=m_nF_n$ is an integer polynomial, a positive rational multiple of $F_n$, with $0<Q_n(\xi)<e^{-cn^2}$.
--
--   This is the assembly step of Fauzan's proof (Section 7), stated for any $\xi$, so it serves both $\zeta(5)$ and $\gamma$.
-- source:
--   A. Fauzan, ζ(5) is irrational (2026), https://zenodo.org/records/22826419, §7; Lean: https://github.com/mo271/zeta5/blob/main/Apery/MainEstimate.lean.

import Mathlib

open Polynomial Filter Topology

namespace HankelIrrationality

theorem decay_of_normalized_family (ξ : ℝ) (F : ℕ → ℚ[X]) (m : ℕ → ℚ) (κ A U : ℝ)
    (hκ : 0 < κ) (hAU : A + U < 0) (hm : ∀ n, 0 < m n)
    (hint : ∀ᶠ n in atTop, ∃ Q : ℤ[X], Q.map (Int.castRingHom ℚ) = C (m n) * F n)
    (hgrowth : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      Real.log (m n) ≤ (A + ε) * (κ * (n : ℝ)) ^ 2)
    (hpos : ∀ᶠ n in atTop, 0 < aeval ξ (F n))
    (hreal : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      Real.log (aeval ξ (F n)) ≤ (U + ε) * (κ * (n : ℝ)) ^ 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∃ Q : ℤ[X],
      (∃ c' : ℚ, 0 < c' ∧ Q.map (Int.castRingHom ℚ) = C c' * F n) ∧
      0 < aeval ξ Q ∧ aeval ξ Q < Real.exp (-c * (n : ℝ) ^ 2) := by sorry

end HankelIrrationality
