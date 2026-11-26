-- Prove2me | Theorems.Thm_LefebvreVariations_mandelbrot_critical_values_le_two_k_le_five
-- name    : LefebvreVariations.mandelbrot_critical_values_le_two_k_le_five
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:16:39.765798+00:00
-- url     : https://prove2.me/theorems/0beb7b2d-ed14-4fd1-9180-1105641ed861
-- title:
--   Lefebvre's variations, No. 183 — on a theme by Douady and Hubbard: the critical values of the first five Mandelbrot polynomials have modulus at most 2
-- statement:
--   Let $p_k(c)=f_c^{\circ k}(0)$ with $f_c(z)=z^2+c$. For every integer $0\le k\le 5$ and every $c\in\mathbb{C}$ with $p_k'(c)=0$,
--   $$
--   |p_k(c)|\le 2 .
--   $$
--
--   The parent asserts this for all $k$; it is the statement that every critical value of the Mandelbrot polynomial $p_k$ lies in the closed disc of radius $2$ (equivalently, that the lemniscate $\{|p_k|\le 2\}$ is as connected as possible). Here only $k\le5$ is claimed, where $p_k$ has degree $2^{k-1}$ and $p_k'$ has degree $2^{k-1}-1\le 15$.
--
--   **Formalization Note** The hypothesis and conclusion are those of `Mandelbrot.mandelbrot_iterate_critical_values_le_two` verbatim (`deriv` of `c ↦ (z ↦ z^2+c)^[k] 0`), with the added hypothesis `k ≤ 5`. For $k=0$ the function is constant and the value is $0$; for $k=1$ the derivative is $1$, so the hypothesis never holds.
--
--   **Why this is a variation.** Variation on the open platform theorem Mandelbrot.mandelbrot_iterate_critical_values_le_two. It is the case k <= 5 with the parent's own formulation, a finite computation with polynomials of degree at most 16; the modulus never exceeds 1.9412 there, so there is room for a rigorous proof by root isolation.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   The parent is the platform theorem Mandelbrot.mandelbrot_iterate_critical_values_le_two (the polynomials p_k(c) = f_c^k(0), f_c(z) = z^2 + c, are the classical Mandelbrot polynomials of Douady-Hubbard, Etude dynamique des polynomes complexes I, Publ. Math. Orsay 84-02, 1984; the exact attribution of the critical-value bound is cited from memory and not checked). Truth check: the author computed all roots of p_k' numerically (mpmath, 40 digits) for k = 2..7; the largest critical-value moduli are 0.25, 1.1527, 1.7624, 1.9412, 1.9854, 1.9964 (all < 2, increasing to 2).

import Mathlib
import Definitions.Def_mandelbrot_sets

set_option autoImplicit false

open Topology Set Function Filter Bornology Metric MeasureTheory

namespace LefebvreVariations

theorem mandelbrot_critical_values_le_two_k_le_five (k : ℕ) (hk : k ≤ 5) (c : ℂ)
    (h : deriv (fun c : ℂ ↦ (fun z ↦ z ^ 2 + c)^[k] 0) c = 0) :
    ‖(fun z ↦ z ^ 2 + c)^[k] 0‖ ≤ 2 := by
  sorry

end LefebvreVariations
