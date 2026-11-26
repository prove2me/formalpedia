-- Prove2me | Theorems.Thm_LefebvreVariations_mandelbrot_lemniscate_isPreconnected_k_le_six
-- name    : LefebvreVariations.mandelbrot_lemniscate_isPreconnected_k_le_six
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:17:13.287065+00:00
-- url     : https://prove2.me/theorems/ab6456b7-253b-414b-9340-77b79bf22fb4
-- title:
--   Lefebvre's variations, No. 184 — on a theme by Douady and Hubbard: the Mandelbrot lemniscate domains of order at most six are connected
-- statement:
--   Let $p_k(c)=f_c^{\circ k}(0)$ with $f_c(z)=z^2+c$. For every integer $0\le k\le 6$, the set
--   $$
--   \{\,c\in\mathbb{C} : |p_k(c)|\le 2\,\}
--   $$
--   is preconnected (connected, as a subset of $\mathbb{C}$).
--
--   The parent states this for all $k$. For a polynomial, the preimage of a closed disc is connected as soon as all critical values lie in the disc; for $k\le 6$ the critical values of $p_k$ have modulus below $1.99$, so this is the finite case in which that criterion applies.
--
--   **Formalization Note** The set and the notion `IsPreconnected` are those of `Mandelbrot.mandelbrot_lemniscate_isPreconnected`, with the extra hypothesis `k ≤ 6`. For $k=0$ the set is all of $\mathbb{C}$, for $k=1$ it is the closed disc of radius $2$.
--
--   **Why this is a variation.** Variation on the open platform theorem Mandelbrot.mandelbrot_lemniscate_isPreconnected: the parent's statement for k <= 6, the first orders beyond the trivial ones (k = 0 whole plane, k = 1 disc). Same set and same notion of connectedness as the parent.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Parent: platform theorem Mandelbrot.mandelbrot_lemniscate_isPreconnected. The criterion used for truth (a polynomial preimage of a closed disc is connected when all critical values lie in the disc, by Riemann-Hurwitz) is classical; it is cited from memory without a page reference. Truth check: the author computed all critical values of p_k numerically for k <= 7 (mpmath, 40 digits); their moduli are 0.25, 1.1527, 1.7624, 1.9412, 1.9854 for k = 2..6, all < 2.

import Mathlib
import Definitions.Def_mandelbrot_sets

set_option autoImplicit false

open Topology Set Function Filter Bornology Metric MeasureTheory

namespace LefebvreVariations

theorem mandelbrot_lemniscate_isPreconnected_k_le_six (k : ℕ) (hk : k ≤ 6) :
    IsPreconnected {c : ℂ | ‖(fun z ↦ z ^ 2 + c)^[k] 0‖ ≤ 2} := by
  sorry

end LefebvreVariations
