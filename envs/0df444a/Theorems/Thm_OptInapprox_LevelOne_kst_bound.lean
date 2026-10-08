-- Prove2me | Theorems.Thm_OptInapprox_LevelOne_kst_bound
-- name    : OptInapprox.LevelOne.kst_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:13.263917+00:00
-- url     : https://prove2.me/theorems/13c718c9-8341-4771-92b2-2cc9b3a00160
-- title:
--   König–Schütt–Tomczak-Jaegermann [40], p. 25 — ‖ℓ‖₁ ≤ √(2/π)‖ℓ‖₂ + (C/2)δ when every coefficient of ℓ is at most δ
-- statement:
--   Let $a_1,\dots,a_n$ be real numbers and $\delta\ge 0$ with $|a_i|\le\delta$ for all $i$, and let $\ell(x)=\sum_{i=1}^n a_i x_i$ on the uniform cube $\{-1,1\}^n$. Then
--   $$\|\ell\|_1\le\sqrt{2/\pi}\,\|\ell\|_2+\frac C2\,\delta,\qquad C=2\Big(1-\sqrt{2/\pi}\Big),$$
--   where $\|\ell\|_1=\mathbf E|\ell|$ and $\|\ell\|_2=\sqrt{\mathbf E[\ell^2]}$.
--
--   A Gaussian with mean zero and standard deviation $\|\ell\|_2$ has $L^1$ norm $\sqrt{2/\pi}\,\|\ell\|_2$; the bound says that a Rademacher sum with small coefficients is close to that value, with an additive error linear in the largest coefficient. The paper takes it from König, Schütt and Tomczak-Jaegermann and uses it, with $a_i=\hat f(\{i\})$, in the proof of Theorem 6.
--
--   **Formalization Note** The hypothesis $\delta\ge0$ is added: for $n\ge 1$ it follows from $|a_1|\le\delta$, and for $n=0$ (where $\ell=0$) it is what makes the right-hand side nonnegative. The constant $C/2=1-\sqrt{2/\pi}$ is written out as `2 * (1 - √(2/π)) / 2`.
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), p. 25, §10.2, Proof of Theorem 6, citing König, Schütt & Tomczak-Jaegermann [40] (J. Reine Angew. Math. 511, 1999)

import Mathlib
import Definitions.Def_OptInapprox_LevelOne_Cube

namespace OptInapprox.LevelOne

theorem kst_bound {n : ℕ} (a : Fin n → ℝ) (δ : ℝ) (hδ0 : 0 ≤ δ) (ha : ∀ i, |a i| ≤ δ) :
    l1Norm (fun x => ∑ i : Fin n, a i * OptInapprox.MaxCut.pm (x i)) ≤
      Real.sqrt (2 / Real.pi) * l2Norm (fun x => ∑ i : Fin n, a i * OptInapprox.MaxCut.pm (x i)) +
        (2 * (1 - Real.sqrt (2 / Real.pi)) / 2) * δ := by sorry

end OptInapprox.LevelOne
