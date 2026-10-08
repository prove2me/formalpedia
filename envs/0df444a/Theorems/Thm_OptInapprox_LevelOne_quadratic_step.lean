-- Prove2me | Theorems.Thm_OptInapprox_LevelOne_quadratic_step
-- name    : OptInapprox.LevelOne.quadratic_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:19.974753+00:00
-- url     : https://prove2.me/theorems/b5f3efeb-3eb4-4af0-8805-a28f791a3d10
-- title:
--   Proof of Theorem 6, p. 25 — X² ≤ √(2/π)X + (C/2)δ ⟹ X ≤ √(1/2π) + √(1/2π + Cδ/2) and X² ≤ 2/π + Cδ
-- statement:
--   Let $C=2(1-\sqrt{2/\pi})$, and let $X\ge 0$ and $\delta\ge 0$ be real numbers with
--   $$X^2\le\sqrt{2/\pi}\,X+\frac C2\,\delta .$$
--   Then
--   $$X\le\sqrt{\frac{1}{2\pi}}+\sqrt{\frac{1}{2\pi}+\frac{C\delta}{2}}\qquad\text{and}\qquad X^2\le\frac{2}{\pi}+C\delta .$$
--
--   This is the last step of the proof of Theorem 6, applied with $X=\|\ell\|_2$: the quadratic inequality obtained from the König–Schütt–Tomczak-Jaegermann bound is solved for $\|\ell\|_2$, and the level-one weight $\|\ell\|_2^2$ is bounded by $2/\pi+C\delta$.
--
--   **Formalization Note** Both conclusions are stated, as on the page. The second does not follow from the first by squaring alone (that leaves a $\sqrt\delta$ term); it is a separate consequence of the quadratic inequality.
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), p. 25, §10.2, Proof of Theorem 6 (last display and sentence)

import Mathlib

namespace OptInapprox.LevelOne

theorem quadratic_step (X δ : ℝ) (hX : 0 ≤ X) (hδ : 0 ≤ δ)
    (h : X ^ 2 ≤ Real.sqrt (2 / Real.pi) * X + (2 * (1 - Real.sqrt (2 / Real.pi)) / 2) * δ) :
    X ≤ Real.sqrt (1 / (2 * Real.pi)) +
        Real.sqrt (1 / (2 * Real.pi) + 2 * (1 - Real.sqrt (2 / Real.pi)) * δ / 2) ∧
    X ^ 2 ≤ 2 / Real.pi + 2 * (1 - Real.sqrt (2 / Real.pi)) * δ := by sorry

end OptInapprox.LevelOne
