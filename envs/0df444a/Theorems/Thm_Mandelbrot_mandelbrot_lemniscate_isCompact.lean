-- Prove2me | Theorems.Thm_Mandelbrot_mandelbrot_lemniscate_isCompact
-- name    : Mandelbrot.mandelbrot_lemniscate_isCompact
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T10:43:51.808367+00:00
-- url     : https://prove2.me/theorems/5d9651e7-140a-4791-9b1e-6943ac42e760
-- title:
--   The filled lemniscates are compact
-- statement:
--   For $k \ge 1$ the filled lemniscate $E_k = \{c : \lVert f_c^{k}(0)\rVert \le 2\}$, with $f_c(z) = z^2 + c$, is compact.
--
--   **Why it is true.** For fixed $k$ the map $c \mapsto f_c^{k}(0)$ is a polynomial in $c$ — by induction, $f_c^{0}(0) = 0$ and $f_c^{k+1}(0) = (f_c^{k}(0))^2 + c$ — hence continuous, so $E_k$ is closed as the preimage of a closed ball. It is bounded because $E_k \subseteq E_1 = \{|c| \le 2\}$ by `Mandelbrot.mandelbrot_lemniscate_antitone`. Closed and bounded in $\mathbb{C}$ is compact.
--
--   **Why $k \ge 1$.** At $k = 0$ the condition reads $\lVert 0 \rVert \le 2$, so $E_0 = \mathbb{C}$, which is closed but not compact. The hypothesis is not removable, and the nested-continuum argument that consumes this statement only needs the tail of the family anyway, since $\bigcap_{k} E_k = \bigcap_{k \ge 1} E_k$.
-- source:
--   Standard; see Carleson and Gamelin, Complex Dynamics, Chapter VIII, or Douady-Hubbard.

import Mathlib
import Definitions.Def_mandelbrot_sets

open Topology Set Function Filter Bornology Metric MeasureTheory

namespace Mandelbrot

theorem mandelbrot_lemniscate_isCompact (k : ℕ) (hk : 1 ≤ k) :
    IsCompact {c : ℂ | ‖(fun z ↦ z ^ 2 + c)^[k] 0‖ ≤ 2} := by sorry

end Mandelbrot
