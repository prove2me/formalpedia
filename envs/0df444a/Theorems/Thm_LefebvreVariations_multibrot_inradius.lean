-- Prove2me | Theorems.Thm_LefebvreVariations_multibrot_inradius
-- name    : LefebvreVariations.multibrot_inradius
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-24T22:39:33.413846+00:00
-- url     : https://prove2.me/theorems/e0c098be-c8ff-4a53-b7ea-51216b04be8b
-- title:
--   Lefebvre's variations, No. 25 — on a theme by Douady and Hubbard: the inradius of the Multibrot sets
-- statement:
--   This determines the largest disc centred at $0$ inside each Multibrot set.
--
--   For $n\ge2$ let $M_n$ be the set of parameters $c\in\mathbb C$ for which the orbit of $0$ under $z\mapsto z^n+c$ does not tend to infinity ($M_2$ is the Mandelbrot set). For $r\ge0$,
--
--   $$
--   \overline{D}(0,r)\subseteq M_n\iff r\le a_n:=\frac{n-1}{n^{n/(n-1)}} .
--   $$
--
--   For $n=2$ this is the classical disc $|c|\le\frac14$. With $p=n^{-1/(n-1)}$ one has $p^n+a_n=p$, so for $|c|\le a_n$ the disc $|z|\le p$ is invariant and the orbit stays bounded; for real $c>a_n$ the inequality $z-z^n\le a_n$ ($z\ge0$) makes the real orbit increase by at least $c-a_n$ at each step, so it escapes.
--
--   The local connectivity of the Multibrot sets is open; this gives their exact inradius about the origin.
--
--   **Formalization Note** Membership uses the mission's `Mandelbrot.multibrotSet n`; the exponent $n/(n-1)$ is a real power.
--
--   **Why this is a variation.** This varies the open problem on the local connectivity of the Multibrot sets (`Mandelbrot.multibrot_locally_connected`, in the Douady–Hubbard theme). It is an unconditional partial result about the same sets: the largest disc centred at $0$ inside $M_n$ has radius $(n-1)/n^{n/(n-1)}$, which is the classical $1/4$ for the Mandelbrot set at $n=2$. It gives the exact inner scale of the sets, complementing the outer escape disc, and so fixes the region around the origin where the connectivity question can be studied explicitly.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Elementary escape estimates for unicritical polynomials z^n + c: R. L. Devaney, An Introduction to Chaotic Dynamical Systems, 2nd ed., Addison-Wesley, 1989, Chapter 1 (real quadratic family) and Chapter 3 (complex quadratic family, the disc |c| ≤ 1/4 in the Mandelbrot set); J. Milnor, Dynamics in One Complex Variable, 3rd ed., Princeton Univ. Press, 2006 (unicritical polynomials and their connectedness loci). Parent problem: Mandelbrot.multibrot_locally_connected.

import Mathlib
import Definitions.Def_mandelbrot_sets

set_option autoImplicit false

open Topology Set Function Filter Bornology Metric

namespace LefebvreVariations

/-- **The largest disc centred at `0` inside the Multibrot set `M_n` has radius
`(n-1)/n^{n/(n-1)}`** (for `n = 2` this is the cusp `1/4` of the Mandelbrot set): the closed disc
of that radius is invariant-by-construction (`|z| ≤ p := n^{-1/(n-1)} ⇒ |zⁿ + c| ≤ pⁿ + |c| ≤ p`),
and every real `c` just beyond it escapes because `z - zⁿ ≤ (n-1)/n^{n/(n-1)}` on `[0, ∞)`.
References: Devaney, *An Introduction to Chaotic Dynamical Systems*, 2nd ed., Addison-Wesley
1989, §1.4 (`n = 2`); Milnor, *Dynamics in One Complex Variable*, 3rd ed., Princeton 2006,
§8 (Multibrot sets `M_n`, parameter space of `z ↦ zⁿ + c`). Complements the platform's
`Mandelbrot.multibrot_escape_criterion` (outer disc) with the inner disc, and the case
`Mandelbrot.multibrotSet n` of `Mandelbrot.multibrot_locally_connected`. -/
theorem multibrot_inradius (n : ℕ) (hn : 2 ≤ n) (r : ℝ) (hr : 0 ≤ r) :
    Metric.closedBall (0 : ℂ) r ⊆ Mandelbrot.multibrotSet n ↔
      r ≤ ((n : ℝ) - 1) / (n : ℝ) ^ ((n : ℝ) / ((n : ℝ) - 1)) := by
  sorry

end LefebvreVariations
