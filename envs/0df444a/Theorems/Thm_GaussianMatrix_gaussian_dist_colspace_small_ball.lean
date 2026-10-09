-- Prove2me | Theorems.Thm_GaussianMatrix_gaussian_dist_colspace_small_ball
-- name    : GaussianMatrix.gaussian_dist_colspace_small_ball
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T03:52:14.159986+00:00
-- url     : https://prove2.me/theorems/170f3de8-6ce5-4bed-976d-3e6bf6d0e2dd
-- title:
--   Distance of a standard Gaussian vector to a fixed subspace: if $\operatorname{rank}B+d\le N$ then $\mathbb P\{\operatorname{dist}(g,\operatorname{col}B)^2\le u\}\le (eu/d)^{d/2}$
-- statement:
--   Let $g$ be a standard Gaussian vector in $\mathbb R^N$ (independent $N(0,1)$ coordinates) and let $B$ be a fixed real $N\times p$ matrix with column space $\operatorname{col}B\subseteq\mathbb R^N$. Let $d\ge1$ be an integer with $\operatorname{rank}B+d\le N$, and let
--   $$\operatorname{dist}(g,\operatorname{col}B)=\inf_{c\in\mathbb R^p}\|g-Bc\|_2 .$$
--   Then for every real $u$ with $0\le u\le d$,
--   $$\mathbb P\big\{\operatorname{dist}(g,\operatorname{col}B)^2\le u\big\}\;\le\;\Big(\frac{e\,u}{d}\Big)^{d/2}.$$
--
--   Choose orthonormal vectors $w_1,\dots,w_d$ in $(\operatorname{col}B)^\perp$ (possible since its dimension is $N-\operatorname{rank}B\ge d$). By Bessel's inequality, $\|g-Bc\|^2\ge\sum_{k\le d}\langle w_k,g-Bc\rangle^2=\sum_{k\le d}\langle w_k,g\rangle^2$ for every $c$. By rotation invariance of the standard Gaussian, $(\langle w_k,g\rangle)_{k\le d}$ is a standard Gaussian vector in $\mathbb R^d$, so the probability is at most $\mathbb P\{\chi^2_d\le u\}\le(eu/d)^{d/2}$.
--
--   This is the fixed-subspace ingredient for small-ball estimates of the smallest singular value: applied conditionally on the other columns of a Gaussian matrix, it controls the distance of one column to the span of the others.
--
--   **Formalization Note.** The law of $g$ is `Measure.pi fun _ : Fin N => gaussianReal 0 1`; $\|v\|_2$ is `Real.sqrt (v ⬝ᵥ v)`; `B.rank` is Mathlib's `Matrix.rank`. The case $p=0$ (trivial subspace) is included.
-- source:
--   standard fact: if V ⊆ R^N is a fixed subspace of dimension ρ and g is standard Gaussian, then ‖P_{V^⊥} g‖² ~ χ²_{N−ρ}; with the χ² lower tail P{χ²_d ≤ u} ≤ (eu/d)^{d/2} for 0 ≤ u ≤ d (Laurent–Massart, Ann. Statist. 28 (2000), Lemma 1, or a Chernoff bound).

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem gaussian_dist_colspace_small_ball {N p d : ℕ} (B : Matrix (Fin N) (Fin p) ℝ)
    (hd : 1 ≤ d) (hrank : B.rank + d ≤ N) (u : ℝ) (hu : 0 ≤ u) (hud : u ≤ d) :
    (Measure.pi fun _ : Fin N => gaussianReal 0 1)
      {g | (⨅ c : Fin p → ℝ, Real.sqrt ((g - B *ᵥ c) ⬝ᵥ (g - B *ᵥ c))) ^ 2 ≤ u}
      ≤ ENNReal.ofReal ((Real.exp 1 * u / d) ^ ((d : ℝ) / 2)) := by sorry

end GaussianMatrix
