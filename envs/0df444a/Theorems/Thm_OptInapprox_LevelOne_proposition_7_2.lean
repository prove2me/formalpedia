-- Prove2me | Theorems.Thm_OptInapprox_LevelOne_proposition_7_2
-- name    : OptInapprox.LevelOne.proposition_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:21.167441+00:00
-- url     : https://prove2.me/theorems/61f55297-7163-474f-b35b-4dea4d49e845
-- title:
--   Proposition 7.2, p. 16 — Inf_i(f) = Σ_{S∋i} f̂(S)²
-- statement:
--   Let $f:\{-1,1\}^n\to\mathbb R$. Then for every coordinate $i\in[n]$,
--   $$\mathrm{Inf}_i(f)=\sum_{S\ni i}\hat f(S)^2 ,$$
--   where $\mathrm{Inf}_i(f)$ is the influence of Definition 2 (the expected variance of $f$ in $x_i$ over a uniform choice of the other coordinates) and the sum runs over all subsets $S\subseteq[n]$ containing $i$.
--
--   This is the Fourier formula for influences, display (5) of the paper. In particular $\hat f(\{i\})^2\le\mathrm{Inf}_i(f)$, which is how a bound on influences controls the coefficients of the linear part of $f$.
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), p. 16, Proposition 7.2, display (5)

import Mathlib
import Definitions.Def_OptInapprox_LevelOne_Cube

namespace OptInapprox.LevelOne

theorem proposition_7_2 {n : ℕ} (f : (Fin n → Bool) → ℝ) (i : Fin n) :
    influence i f = ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => i ∈ S), OptInapprox.MaxCut.fourier f S ^ 2 := by sorry

end OptInapprox.LevelOne
