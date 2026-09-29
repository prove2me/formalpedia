-- Prove2me | Theorems.Thm_ModularCurve_exists_meromorphic_logDeriv_eq_of_int_residue
-- name    : ModularCurve.exists_meromorphic_logDeriv_eq_of_int_residue
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/d02421d5-1d4e-5c92-88a2-0ce722fb49ba
-- title:
--   Exponentiating a form with simple poles and integer residues
-- statement:
--   Let $m : \mathbb{C} \to \mathbb{Z}$ and $\omega : \mathbb{C} \to \mathbb{C}$ be arbitrary functions, subject to the following hypothesis at each point $a$ of the open upper half-plane (i.e. each $a$ with $\operatorname{Im} a > 0$): there is a function $g : \mathbb{C} \to \mathbb{C}$, analytic at $a$, such that $\omega(z) = m(a)/(z-a) + g(z)$ for all $z$ in a punctured neighbourhood of $a$ (that is, eventually in the filter $\mathcal{N}[\neq] a$ of deleted neighbourhoods), and such that $\omega(a) = g(a)$ in case $m(a) = 0$. The conclusion asserts the existence of a single function $G : \mathbb{C} \to \mathbb{C}$ with the following properties at every $a$ in the upper half-plane: $G$ is meromorphic at $a$; its meromorphic order at $a$, as an element of $\mathbb{Z} \cup \{\infty\}$, equals $m(a)$; if $m(a) \neq 0$ then the value $G(a)$ is $0$; and if $m(a) = 0$ then $G$ is analytic at $a$, $G(a) \neq 0$, and $G$ is differentiable at $a$ with derivative $\omega(a)\,G(a)$. Nothing is asserted about $G$ outside the upper half-plane.
--
--   This is the solution of the multiplicative Cousin problem on the simply connected domain $\mathfrak{H}$: a differential with at worst simple poles and integral residues is the logarithmic derivative $dG/G$ of a meromorphic function whose divisor is $\sum_a m(a)\cdot a$, obtained classically as $\exp \int \omega$. It is used by [`ModularCurve.exists_meromorphic_smul_eq_mul_of_slashInvariant_residue`](thm.html#ModularCurve.exists_meromorphic_smul_eq_mul_of_slashInvariant_residue) to pass from a weight-one logarithmic-derivative datum invariant under a congruence subgroup to an actual meromorphic function transforming accordingly.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_meromorphic_logDeriv_eq_of_int_residue.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Topology

theorem ModularCurve.exists_meromorphic_logDeriv_eq_of_int_residue
    (m : ℂ → ℤ) (ω : ℂ → ℂ)
    (hres : ∀ a : ℂ, 0 < a.im → ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
      (∀ᶠ z in 𝓝[≠] a, ω z = (m a : ℂ) / (z - a) + g z) ∧ (m a = 0 → ω a = g a)) :
    ∃ G : ℂ → ℂ, ∀ a : ℂ, 0 < a.im →
      MeromorphicAt G a ∧ meromorphicOrderAt G a = (m a : WithTop ℤ) ∧
      (m a ≠ 0 → G a = 0) ∧
      (m a = 0 → AnalyticAt ℂ G a ∧ G a ≠ 0 ∧ HasDerivAt G (ω a * G a) a) := by sorry
