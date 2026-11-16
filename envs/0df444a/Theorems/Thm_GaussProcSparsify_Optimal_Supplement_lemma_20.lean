-- Prove2me | Theorems.Thm_GaussProcSparsify_Optimal_Supplement_lemma_20
-- name    : GaussProcSparsify.Optimal.Supplement.lemma_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:21:14.602513+00:00
-- url     : https://prove2.me/theorems/f62c266c-a3e1-4f31-9e2b-e4597c15944f
-- title:
--   Lemma 20 — radial affine approximation needs exponentially many pieces
-- statement:
--   There are universal constants $c_0,\kappa>0$ and a universal positive integer $N_0$ such that, for every $n\ge N_0$, every $m>0$, every family $u_1,\ldots,u_m\in S^{n-1}$ and every real family $a_1,\ldots,a_m$, the function $h(g)=\max_j\{a_j+\langle g,u_j\rangle/\sqrt n\}$ satisfies
--   $$\left\|\frac{\|g\|_2}{\sqrt n}-h(g)\right\|_{L^2(\gamma_n)}\le\frac{\kappa}{\sqrt n}\quad\Longrightarrow\quad m\ge e^{c_0n}.$$
--   This is the radial approximation obstruction supporting the sparsification lower bound of Theorem 2.
--
--   Differences from the source:
--   - encoding: Euclidean R^n → EuclideanSpace ℝ (Fin n); reason: the fixed Euclidean coordinates, inner product and standard Gaussian law are preserved
--   - encoding: finite maxima and Gaussian L² norms → nonempty finite families and extended eLpNorm bounds; reason: maxima are defined on exactly their nonempty domains, and infinite error cannot become zero
--   - encoding: universal constants in asymptotic notation → positive existential constants before all instance parameters; reason: spells out the uniformity of the source bounds without selecting a numerical constant
--   - encoding: all sufficiently large n → a positive universal N₀ with n≥N₀; reason: makes the dimension threshold explicit and avoids the undefined n=0 normalization
-- source:
--   Shivam Nadimpalli, Optimal Sparsification of Gaussian Processes, STOC 2027 submission #163 (October 2026), Lemma 20, PDF p. 31 (printed p. 30), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/163.pdf

import Definitions.Def_GaussProcSparsify_Optimal_Supplement_Approximation

open MeasureTheory ProbabilityTheory

namespace GaussProcSparsify.Optimal.Supplement

/-- Lemma 20, PDF pp. 31–32. All constants and the dimension threshold are universal. -/
theorem lemma_20 :
    ∃ c₀ κ : ℝ, 0 < c₀ ∧ 0 < κ ∧ ∃ N₀ : ℕ, 0 < N₀ ∧
      ∀ n : ℕ, N₀ ≤ n → ∀ m : ℕ, 0 < m →
        ∀ (u : Fin m → Vec n) (a : Fin m → ℝ), (∀ j, ‖u j‖ = 1) →
          eLpNorm (fun g => ‖g‖ / Real.sqrt n - radialAffineMax u a g) 2 (gaussian n) ≤
            ENNReal.ofReal (κ / Real.sqrt n) →
          Real.exp (c₀ * n) ≤ (m : ℝ) := by sorry

end GaussProcSparsify.Optimal.Supplement
