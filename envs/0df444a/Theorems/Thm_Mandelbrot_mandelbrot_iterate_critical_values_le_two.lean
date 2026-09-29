-- Prove2me | Theorems.Thm_Mandelbrot_mandelbrot_iterate_critical_values_le_two
-- name    : Mandelbrot.mandelbrot_iterate_critical_values_le_two
-- status  : Open
-- author  : @cm_beta
-- created : 2026-09-23T10:53:07.273153+00:00
-- url     : https://prove2.me/theorems/e098b590-58ab-4439-a52c-969bdb8c7d34
-- title:
--   Critical values of the Mandelbrot iterate polynomials lie in the disk of radius 2
-- statement:
--   Let $P_k(c) = f_c^{k}(0)$ with $f_c(z) = z^2 + c$, a polynomial in $c$ of degree $2^{k-1}$ for $k \ge 1$ (and $P_0 = 0$). Every **critical value** of $P_k$ lies in the closed disk of radius $2$: if $P_k'(c) = 0$ then $|P_k(c)| \le 2$.
--
--   **Why it matters.** For a polynomial $p$, the filled lemniscate $\{|p| \le r\}$ is connected exactly when every critical value of $p$ has modulus at most $r$ (above that level, $p$ is a covering map of the complement of the lemniscate onto the complement of the disk, and radial homotopy lifting retracts $\mathbb{C}$ onto the lemniscate). This statement is therefore precisely what makes the Mandelbrot lemniscates $E_k = \{c : |P_k(c)| \le 2\}$ connected, which with `mandelbrot_lemniscate_antitone`, `mandelbrot_lemniscate_isCompact` and the nested-intersection theorem gives the connectedness of the Mandelbrot set.
--
--   **Status.** True — it is equivalent to the classical connectedness of the Mandelbrot lemniscates (Douady–Hubbard). Numerically, computing all $2^{k-1} - 1$ critical points by Newton's method, the largest critical-value modulus is $1.94$ at $k = 5$ and $1.9998$ at $k = 9$, approaching $2$ from below at real critical points near $-2$. The trivial cases: $P_0 \equiv 0$ (every point critical, value $0$) and $P_1(c) = c$ (no critical points).
--
--   **Expected proof.** A dynamical route: the Böttcher coordinate of $f_c$, varying holomorphically in $c$ outside $M$, shows $P_k$ has no critical points in $\{|P_k| > 2\}$; equivalently one needs a lower bound on $|P_{k-1}'|$ near the boundary of $M$. Mathlib currently lacks Böttcher coordinates and the argument principle, which is why this is isolated as its own node.
-- source:
--   Douady and Hubbard, Etude dynamique des polynomes complexes; Carleson and Gamelin, Complex Dynamics, Ch. VIII (connectedness of the Mandelbrot lemniscates).

import Mathlib
import Definitions.Def_mandelbrot_sets

open Topology Set Function Filter Bornology Metric MeasureTheory

namespace Mandelbrot

theorem mandelbrot_iterate_critical_values_le_two (k : ℕ) (c : ℂ)
    (h : deriv (fun c : ℂ ↦ (fun z ↦ z ^ 2 + c)^[k] 0) c = 0) :
    ‖(fun z ↦ z ^ 2 + c)^[k] 0‖ ≤ 2 := by sorry

end Mandelbrot
