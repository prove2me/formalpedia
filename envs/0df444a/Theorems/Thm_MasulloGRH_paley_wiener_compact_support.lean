-- Prove2me | Theorems.Thm_MasulloGRH_paley_wiener_compact_support
-- name    : MasulloGRH.paley_wiener_compact_support
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-21T18:37:54.811187+00:00
-- url     : https://prove2.me/theorems/1a7c78d8-7a0b-4271-8738-b87884e97bbc
-- title:
--   Theorem 4.2.2.1 — Paley–Wiener theorem for Fourier transforms of $L^2$ functions on $(-A,A)$
-- statement:
--   Let $A>0$ and let $f$ be an entire function. The following are equivalent:
--
--   1. there is a function $F\in L^2((-A,A))$ such that
--   $$f(z)=\int_{-A}^{A}F(x)\,e^{ixz}\,dx\qquad\text{for all }z\in\mathbb C;$$
--   2. there is a constant $C>0$ with $|f(z)|\le C\,e^{A|z|}$ for all $z\in\mathbb C$, and the restriction of $f$ to the real line is in $L^2(\mathbb R)$.
--
--   This is the classical Paley–Wiener theorem. Through the change of variables $x=-i\log t$ it characterizes the Mellin transforms of square integrable functions supported in $[1/A,A]\subset\mathbb R_{>0}$, which the draft uses to build bases of compactly supported functions.
--
--   **Formalization Note** The normalization of the Lebesgue measure does not affect either condition.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Chapter 4, §4.2.2, Theorem 4.2.2.1 (Paley-Wiener Theorem on compactly supported Fourier transforms), eq. (4.2.2.1), pp. 170–171

import Definitions.Def_MasulloGRH_SchauderBases

set_option autoImplicit false

namespace MasulloGRH

open MeasureTheory

theorem paley_wiener_compact_support (A : ℝ) (hA : 0 < A) (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) :
    (∃ F : ℝ → ℂ, MemLp F 2 (volume.restrict (Set.Ioo (-A) A)) ∧
      ∀ z : ℂ, f z = ∫ x in (-A)..A, F x * Complex.exp (Complex.I * x * z)) ↔
    ((∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (A * ‖z‖)) ∧
      MemLp (fun x : ℝ => f x) 2 volume) := by sorry

end MasulloGRH
