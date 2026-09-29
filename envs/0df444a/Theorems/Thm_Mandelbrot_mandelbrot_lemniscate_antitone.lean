-- Prove2me | Theorems.Thm_Mandelbrot_mandelbrot_lemniscate_antitone
-- name    : Mandelbrot.mandelbrot_lemniscate_antitone
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T10:43:44.352554+00:00
-- url     : https://prove2.me/theorems/88525285-f9d7-4d79-a620-d9b9f50f5473
-- title:
--   The filled lemniscates decrease
-- statement:
--   Write $f_c(z) = z^2 + c$ and $E_k = \{c \in \mathbb{C} : \lVert f_c^{k}(0)\rVert \le 2\}$, the $k$-th filled lemniscate. Then $E_{k+1} \subseteq E_k$: the lemniscates decrease.
--
--   **Why it is true.** The content is the escape lemma. For $k \ge 1$ one has $\lVert f_c^{k}(0)\rVert \ge |c|$ by induction, so if $|z| = \lVert f_c^{k}(0)\rVert > 2$ then
--   $$\lVert f_c^{k+1}(0)\rVert = |z^2 + c| \ge |z|^2 - |c| \ge |z|^2 - |z| = |z|(|z|-1) > |z| > 2 .$$
--   So once the orbit of the critical point passes modulus $2$ it strictly increases and never returns; contrapositively, $\lVert f_c^{k+1}(0)\rVert \le 2$ forces $\lVert f_c^{k}(0)\rVert \le 2$. At $k = 0$ the statement is trivial because $f_c^{0}(0) = 0$.
--
--   **What it is for.** `Mandelbrot.mandelbrot_escape_criterion` identifies the Mandelbrot set with $\bigcap_k E_k$. Each $E_k$ is compact (for $k \ge 1$) and preconnected, but an intersection of preconnected sets is not preconnected in general — the family has to be *nested*. This statement supplies that, and together with compactness it is what lets the nested-continuum argument apply.
--
--   Note $E_0 = \mathbb{C}$, so the family is decreasing from the start but only becomes bounded at $k = 1$, where $E_1 = \{|c| \le 2\}$.
-- source:
--   Douady and Hubbard, Etude dynamique des polynomes complexes; the escape criterion is standard, see Carleson and Gamelin, Complex Dynamics, Chapter VIII.

import Mathlib
import Definitions.Def_mandelbrot_sets

open Topology Set Function Filter Bornology Metric MeasureTheory

namespace Mandelbrot

theorem mandelbrot_lemniscate_antitone (k : ℕ) :
    {c : ℂ | ‖(fun z ↦ z ^ 2 + c)^[k + 1] 0‖ ≤ 2} ⊆
      {c : ℂ | ‖(fun z ↦ z ^ 2 + c)^[k] 0‖ ≤ 2} := by sorry

end Mandelbrot
