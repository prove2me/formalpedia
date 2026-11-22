-- Prove2me | Theorems.Thm_HardyLittlewoodMaximal_strongType_euclidean
-- name    : HardyLittlewoodMaximal.strongType_euclidean
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:49:08.388509+00:00
-- url     : https://prove2.me/theorems/95fec70a-2e12-4df4-b405-357639b2973b
-- title:
--   Hardy–Littlewood maximal theorem on $\mathbb R^d$: $\|Mf\|_p^p\le\frac{2^p\,3^d\,p}{p-1}\|f\|_p^p$ for $p>1$
-- statement:
--   **Hardy–Littlewood maximal theorem on $\mathbb R^d$, strong type $(p,p)$ with an explicit constant.** Let $d\ge 0$ be an integer, let $m$ be Lebesgue measure on $\mathbb R^d$, and for a measurable $f\colon\mathbb R^d\to\mathbb C$ let
--   $$(Mf)(x)\;=\;\sup_{r>0}\ \frac1{m(B(x,r))}\int_{B(x,r)}|f(y)|\,dy\ \in[0,\infty],\qquad x\in\mathbb R^d ,$$
--   be the (centred) Hardy–Littlewood maximal function, $B(x,r)$ being the open Euclidean ball. Let $p>1$ be a real number and $f\in L^p(\mathbb R^d)$. Then
--   $$\int_{\mathbb R^d}(Mf)(x)^p\,dx\;\le\;\frac{2^p\,3^d\,p}{p-1}\int_{\mathbb R^d}|f(x)|^p\,dx ,$$
--   that is, $\|Mf\|_{L^p}\le 2\big(\tfrac{3^d p}{p-1}\big)^{1/p}\|f\|_{L^p}$.
--
--   This is the $d$-dimensional analogue of inequality (A.5.1.4) of the source (which is the case $d=1$, with constant $\frac{2^p\cdot 3p}{p-1}$): the source notes in Remark A.5.1.2 that the argument for Theorem A.5.1.1(3) generalizes to $\mathbb R^d$, and that argument turns the weak type constant $3^d$ into the constant displayed here.
--
--   **Formalization Note.** $M$ is the platform definition `DbarRegularity.maximalFunction` on `EuclideanSpace ℝ (Fin d)`, with values in $[0,\infty]$; both sides are integrals of non-negative extended real functions. The source does not write out the $d$-dimensional constant; the one stated is what its one-dimensional proof gives with $3$ replaced by $3^d$. The platform already has the existence of a constant (`DbarRegularity.maximalFunction_strongType`).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 568, Remark A.5.1.2 (d-dimensional analogue of Theorem A.5.1.1(3), eq. (A.5.1.4), p. 566)

import Mathlib
import Definitions.Def_DbarRegularity_Setting

open MeasureTheory Metric Filter Topology Pointwise
open scoped ENNReal NNReal

set_option autoImplicit false

namespace HardyLittlewoodMaximal

theorem strongType_euclidean (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℂ) (p : ℝ) (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    ∫⁻ x, DbarRegularity.maximalFunction f x ^ p ≤
      ENNReal.ofReal (2 ^ p * 3 ^ d * p / (p - 1)) * ∫⁻ x, ‖f x‖ₑ ^ p := by sorry

end HardyLittlewoodMaximal
