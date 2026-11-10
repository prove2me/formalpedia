-- Prove2me | Theorems.Thm_OptRobustCD_lemma_5_9
-- name    : OptRobustCD.lemma_5_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:51:14.597216+00:00
-- url     : https://prove2.me/theorems/2face383-ffe1-4202-b1ef-d7cff158bcb3
-- title:
--   Lemma 5.9 — robust recovery of a delocalized negative eigenvector with probability $1-n^{-10}$ (corrected: leading constant in the operation counts)
-- statement:
--   There is a randomized algorithm and absolute constants $K_0,c_0$ with the following properties. Let $\varepsilon,g>0$ and let $M,\tilde M\in\mathbb R^{n\times n}$ be symmetric, with $M$ having exactly one negative eigenvalue $-g$. Suppose there is a unit vector $w\in\mathbb R^n$ with
--   $$\|w\|_4^4\le\frac1{\varepsilon n}\qquad\text{and}\qquad w^\top Mw\le-(1-\varepsilon)g,$$
--   and suppose $\|\tilde M-M\|_{1,2}\le\varepsilon g\sqrt n$. Given matrix-vector access to $\tilde M$, an upper bound $C\ge\|\tilde M\|_{1,\infty}+1$, and $\varepsilon$ (but not $g$) as inputs, the algorithm returns a unit vector $\hat w$ such that, with probability at least $1-n^{-10}$ over its internal randomness,
--   $$\langle\hat w,w\rangle^2\ge1-K_0\sqrt\varepsilon,$$
--   and on the same event it performs at most $c_0(1+C\log n/(\varepsilon g))^{c_0}$ matrix-vector products with $\tilde M$ and at most $n$ times as many additional operations.
--
--   It is the robust spectral step of Theorem 5.1.
--
--   Differences from the source:
--   - reading: a randomized algorithm … returns a unit vector ŵ; O(√ε), O(1) → one real-RAM program and absolute K₀, c₀ chosen before ε, g, n, M, M̃; input [n, C, ε], M̃ only through the oracle; on the event the run halts within c₀(1 + C log n/(εg))^{c₀} oracle calls and n times as many other steps, with output a unit vector ŵ; reason: the paper names no machine; O(·) is an absolute constant
--   - correction: at most (1 + C log n/(εg))^{O(1)} matrix-vector products and at most n times as many additional operations → at most c₀·(1 + C log n/(εg))^{c₀} oracle calls and n·c₀·(1 + C log n/(εg))^{c₀} other steps; reason: read literally the printed count is false, since its base tends to 1 as g → ∞: n = 2, ε = 1, M = diag(−g, 0), M̃ = 0, C = 1, w = (1, 1)/√2 satisfy every hypothesis, the bound then allows at most one oracle call and two other steps for large g, and no run can set the output length to 2 and halt within two steps with a unit output (the block read is [2, 1] or [0, 0]); a leading constant is the minimal fix
--   - encoding: exactly one negative eigenvalue −g → the multiset of negative eigenvalues (real roots of the characteristic polynomial, with multiplicity) is {−g}; reason: equal for symmetric matrices
--   - encoding: with probability at least 1 − n^{−10} → the outer tape measure of the failure set is at most n^{−10}; reason: the outer measure bounds the failure probability from above, so measurability is not needed
-- source:
--   Hopkins, Hua, Mohanty, Rajaraman, Steurer, Optimal Robust Community Detection, STOC 2027 submission (manuscript of November 3, 2026, sha256 3d287d5422db7c4a43e74333bda1dbed204af51a25fd9f2c6e875ae03a4dafa1), Lemma 5.9, p.27 (pdf p.29)

import Mathlib
import Definitions.Def_OptRobustCD_Machine
import Definitions.Def_OptRobustCD_DirEdges
import Definitions.Def_OptRobustCD_RowNorms

namespace OptRobustCD

/-- **Lemma 5.9** (Robust recovery of a delocalized negative eigenvector). Hopkins, Hua, Mohanty, Rajaraman, Steurer, *Optimal Robust Community
Detection*, STOC 2027 submission (manuscript of November 3, 2026, sha256 3d287d54…), Lemma 5.9,
p.27 (pdf p.29).

"There is a randomized algorithm with the following properties. Let ε, g > 0 and
`M, M̃ ∈ R^{n×n}` be symmetric, with M having exactly one negative eigenvalue −g. Suppose there
exists a unit vector `w ∈ R^n` satisfying `∥w∥⁴_4 ⩽ 1/(εn)` and `w^⊤Mw ⩽ −(1 − ε)g`. Suppose also
that `∥M̃ − M∥_{1,2} ⩽ εg√n`. Then, given matrix-vector access to `M̃`, an upper bound
`C ⩾ ∥M̃∥_{1,∞} + 1`, and ε (but not g) as inputs, the algorithm returns a unit vector ŵ such that
with probability at least `1 − n^{−10}` over the internal randomness of the algorithm,
`⟨ŵ, w⟩² ⩾ 1 − O(√ε)`. On the same event, the algorithm performs at most
`(1 + C log n/(εg))^{O(1)}` matrix-vector products with `M̃` and at most n times as many additional
operations."

**Formalization Note.**
* One program `prog` of the real RAM and universal constants `K₀, c₀`, chosen before `ε, g, n, M, M̃`
  (the `O(·)`s are absolute). Input `[n, C, ε]`; `M̃` only through the oracle `x ↦ M̃x`.
* "Exactly one negative eigenvalue −g": the negative eigenvalues of `M` with multiplicity are the
  multiset `{−g}`.
* The event: the run halts after at most `c₀ (1 + C log n/(εg))^{c₀}` oracle calls and at most `n`
  times as many other steps, with output a unit vector `ŵ` (as `n` reals) and
  `⟨ŵ, w⟩² ⩾ 1 − K₀√ε`. Its complement has (outer) tape measure at most `n^{−10}`.
* **Correction (leading constant).** The printed counts `(1 + C log n/(εg))^{O(1)}` and "n times as
  many" carry no constant factor, and the base tends to `1` as `g → ∞`. Read literally the lemma is
  false: at `n = 2`, `ε = 1`, `M = diag(−g, 0)`, `M̃ = 0`, `C = 1`, `w = (1, 1)/√2` every hypothesis
  holds, yet for `g` large the bound allows at most one oracle call (returning `0`) and two other
  steps, and no run that sets the output length to `2` and halts in two steps outputs a unit
  vector (the block read is `[2, 1]` or `[0, 0]`). The leading factor `c₀` is the minimal fix. -/
theorem lemma_5_9 :
    ∃ K₀ : ℝ, ∃ c₀ : ℕ, ∃ prog : Program, ∀ ε g : ℝ, 0 < ε → 0 < g →
      ∀ (n : ℕ) (M Mt : Matrix (Fin n) (Fin n) ℝ), M.IsSymm → Mt.IsSymm → negEigs M = {-g} →
      ∀ w : Fin n → ℝ, l2 w = 1 → l4pow4 w ≤ 1 / (ε * n) → w ⬝ᵥ M.mulVec w ≤ -(1 - ε) * g →
      norm12 (Mt - M) ≤ ε * g * Real.sqrt n → ∀ C : ℝ, norm1inf Mt + 1 ≤ C →
        tapeMeasure {ω | ¬ HaltsWithCounts prog (matOracle Mt) [(n : ℝ), C, ε] ω
          (c₀ * (1 + C * Real.log n / (ε * g)) ^ c₀)
          (n * (c₀ * (1 + C * Real.log n / (ε * g)) ^ c₀))
          (fun out => ∃ wh : Fin n → ℝ, out = List.ofFn wh ∧ l2 wh = 1 ∧
            1 - K₀ * Real.sqrt ε ≤ ip wh w ^ 2)} ≤
          ENNReal.ofReal ((n : ℝ) ^ (-(10 : ℤ))) := by sorry

end OptRobustCD
