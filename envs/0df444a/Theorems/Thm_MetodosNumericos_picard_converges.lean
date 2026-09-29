-- Prove2me | Theorems.Thm_MetodosNumericos_picard_converges
-- name    : MetodosNumericos.picard_converges
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T16:51:23.305368+00:00
-- url     : https://prove2.me/theorems/a25edf45-b5fe-41fc-b52e-41f925b81dd9
-- title:
--   The Picard iterates converge to the solution
-- statement:
--   Under the hypotheses of the previous milestone, $y_k(x) \\to \\varphi(x)$ as $k \\to \\infty$, for every $x \\in [x_0-h, x_0+h]$. This is the limit statement that closes §9.5.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 9, §9.5, p. 186 ("lim y_k(x) = φ(x)").

import Mathlib
import Definitions.Def_MetodosNumericos_edoDefs

open Filter Topology

namespace MetodosNumericos

theorem picard_converges (f : ℝ → ℝ → ℝ) (phi : ℝ → ℝ) (x0 y0 a b M N h : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hM : 0 < M) (hN : 0 ≤ N) (hh : h = min a (b / M))
    (hbound : ∀ x ∈ Set.Icc (x0 - a) (x0 + a), ∀ y ∈ Set.Icc (y0 - b) (y0 + b), |f x y| ≤ M)
    (hlip : ∀ x ∈ Set.Icc (x0 - a) (x0 + a), ∀ u ∈ Set.Icc (y0 - b) (y0 + b),
      ∀ v ∈ Set.Icc (y0 - b) (y0 + b), |f x u - f x v| ≤ N * |u - v|)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2)
      (Set.Icc (x0 - a) (x0 + a) ×ˢ Set.Icc (y0 - b) (y0 + b)))
    (hphi0 : phi x0 = y0)
    (hsol : ∀ x ∈ Set.Icc (x0 - h) (x0 + h), HasDerivAt phi (f x (phi x)) x)
    (hrange : ∀ x ∈ Set.Icc (x0 - h) (x0 + h), phi x ∈ Set.Icc (y0 - b) (y0 + b))
    (x : ℝ) (hx : x ∈ Set.Icc (x0 - h) (x0 + h)) :
    Tendsto (fun k => picardSeq f x0 y0 k x) atTop (𝓝 (phi x)) := by sorry

end MetodosNumericos
