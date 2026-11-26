-- Prove2me | Theorems.Thm_LefebvreVariations_mandelbrot_real_slice
-- name    : LefebvreVariations.mandelbrot_real_slice
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-24T22:19:41.315933+00:00
-- url     : https://prove2.me/theorems/bf79ae8f-8f4e-460d-981a-923226b36545
-- title:
--   Lefebvre's variations, No. 11 — on a theme by Douady and Hubbard: the real slice of the Mandelbrot set is $[-2,1/4]$
-- statement:
--   This is the real slice of the Mandelbrot set.
--
--   Let $M\subseteq\mathbb C$ be the Mandelbrot set: the parameters $c$ for which the orbit $z_0=0$, $z_{n+1}=z_n^2+c$ does not tend to infinity. Then
--
--   $$
--   M\cap\mathbb R=[-2,\tfrac14].
--   $$
--
--   For real $c$ the orbit is real. When $-2\le c\le 0$ it stays in $[-|c|,|c|]$, and when $0\le c\le\frac14$ it stays in $[0,\frac12]$, so it is bounded. When $c>\frac14$ every step increases $z_n$ by at least $c-\frac14$, and when $c<-2$ the orbit grows by at least $|c|(|c|-2)$ per step after two steps, so in both cases it escapes.
--
--   The local connectivity of $M$ (MLC, Douady–Hubbard) is open; along the real axis the set is the segment above, the first place where its structure is completely explicit.
--
--   **Formalization Note** Membership uses the mission's `Mandelbrot.mandelbrotSet`; a real parameter $x$ is identified with the complex number $(x:\mathbb C)$.
--
--   **Why this is a variation.** This varies the Mandelbrot set statements on the platform, the open conjecture that the Mandelbrot set is locally connected. It is a special case about the same set along the real axis, where the set is understood: its intersection with $\mathbb{R}$ is the interval $[-2,1/4]$. It fixes the set's definitions on the real slice, a basic sanity check for any work on the parent.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   A. Douady and J. H. Hubbard, Étude dynamique des polynômes complexes, Partie I, Publications Mathématiques d'Orsay 84-02 (1984); R. L. Devaney, An Introduction to Chaotic Dynamical Systems, 2nd ed., Addison-Wesley, 1989, Chapter 1 (real quadratic family x ↦ x² + c and its bifurcation interval [−2, 1/4]). Parent problem: Mandelbrot.mandelbrot_locally_connected (MLC).

import Mathlib
import Definitions.Def_mandelbrot_sets

set_option autoImplicit false

open Topology Set Function Filter Bornology Metric

namespace LefebvreVariations

/-- **The real slice of the Mandelbrot set** is the interval `[-2, 1/4]`: Douady–Hubbard,
*Étude dynamique des polynômes complexes I*, Publ. Math. Orsay 84-02 (1984), §III.4 (the real
quadratic family); also Devaney, *An Introduction to Chaotic Dynamical Systems*, 2nd ed.,
Addison-Wesley 1989, §1.4 (the exceptional parameters `c = -2` and `c = 1/4`). It is the
intersection of the set whose local connectivity is `Mandelbrot.mandelbrot_locally_connected`
with the real axis. -/
theorem mandelbrot_real_slice :
    {x : ℝ | (x : ℂ) ∈ Mandelbrot.mandelbrotSet} = Set.Icc (-2 : ℝ) (1 / 4) := by
  sorry

end LefebvreVariations
