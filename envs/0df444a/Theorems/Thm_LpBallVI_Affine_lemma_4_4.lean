-- Prove2me | Theorems.Thm_LpBallVI_Affine_lemma_4_4
-- name    : LpBallVI.Affine.lemma_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:11:07.724385+00:00
-- url     : https://prove2.me/theorems/fbef65f4-47f2-4b21-b058-d082e4306df2
-- title:
--   Lemma 4.4 — k_λ is nonnegative, 2-Lipschitz, ≤ 17; bounded below near 2 with tail c_k|t|^{−β_p}, β_p > 2; κ_k = poly(ε_k)
-- statement:
--   Let $1 < p < \infty$, $p \ne 2$. (i) For every $\lambda > 0$, $k_\lambda \ge 0$, $k_\lambda$ is 2-Lipschitz and $|k_\lambda(t)| \le 17$. (ii) There are rationals $c_0, r_0 > 0$ and reals $c_k > 0$, $\beta_p > 2$, depending only on $p$, such that for every $\lambda \in [1/2, 2]$
--   $$k_\lambda(t) \ge c_0 \ \ (|t - 2| \le r_0), \qquad k_\lambda(t) \le c_k |t|^{-\beta_p}\ \ (|t| \ge 4).$$
--   (iii) For every $\epsilon_k > 0$ there is $\kappa_k = \mathrm{poly}(\epsilon_k) > 0$ with $|\lambda - 1| \le \kappa_k \Rightarrow \|k_\lambda - k_1\|_\infty \le \epsilon_k$; read as: there are $C, e > 0$ (depending only on $p$) such that some such $\kappa_k \ge C\min\{1,\epsilon_k\}^e$ exists for every $\epsilon_k$. These are the properties of the weight function that make the grid approximation of Lemma 4.6 work.
--
--   Differences from the source:
--   - reading: κ_k = poly(ϵ_k) > 0 → ∃ C, e > 0 depending only on p such that for every ϵ_k > 0 some κ_k with κ_k ≥ C·min{1, ϵ_k}^e works; reason: 'poly' read as a polynomial lower bound on the admissible neighbourhood of λ = 1
--   - encoding: ‖k_λ − k_1‖_∞ ≤ ϵ_k → |k_λ(t) − k_1(t)| ≤ ϵ_k for every t; reason: sup norm written pointwise
-- source:
--   Anagnostides, Panageas, Yan, On the Role of Geometry in Solving Variational Inequalities, arXiv:2611.04151 (held copy, sha256 a3f8212d…0a5cbe), p. 21, Lemma 4.4, (17), (18)

import Mathlib
import Definitions.Def_LpBallVI_Affine_Sigma

namespace LpBallVI.Affine

/-- **Lemma 4.4**, p. 21, for `1 < p < ∞`, `p ≠ 2`. (i) For `λ > 0`, `k_λ ≥ 0`, `k_λ` is 2-Lipschitz
and `|k_λ| ≤ 17`. (ii) There are rationals `c₀, r₀ > 0` and reals `c_k > 0`, `β_p > 2` (depending
only on `p`) with `k_λ(t) ≥ c₀` for `|t − 2| ≤ r₀` and `k_λ(t) ≤ c_k |t|^{−β_p}` for `|t| ≥ 4`, for
every `λ ∈ [1/2, 2]`. (iii) `κ_k = poly(ε_k)`: there are `C, e > 0` such that for every `ε_k > 0`
some `κ_k ≥ C min{1, ε_k}^e` gives `‖k_λ − k₁‖_∞ ≤ ε_k` whenever `|λ − 1| ≤ κ_k`. -/
theorem lemma_4_4 (p : ℝ) (hp : 1 < p) (hp2 : p ≠ 2) :
    (∀ lam : ℝ, 0 < lam →
      (∀ t, 0 ≤ kLam p lam t) ∧
        (∀ s t, |kLam p lam s - kLam p lam t| ≤ 2 * |s - t|) ∧
        (∀ t, |kLam p lam t| ≤ 17)) ∧
    (∃ c0 r0 : ℚ, 0 < c0 ∧ 0 < r0 ∧ ∃ ck βp : ℝ, 0 < ck ∧ 2 < βp ∧
      ∀ lam : ℝ, 1 / 2 ≤ lam → lam ≤ 2 →
        (∀ t, |t - 2| ≤ (r0 : ℝ) → (c0 : ℝ) ≤ kLam p lam t) ∧
        (∀ t, 4 ≤ |t| → kLam p lam t ≤ ck * |t| ^ (-βp))) ∧
    (∃ C e : ℝ, 0 < C ∧ 0 < e ∧ ∀ εk : ℝ, 0 < εk → ∃ κk : ℝ, 0 < κk ∧ C * min 1 εk ^ e ≤ κk ∧
      ∀ lam : ℝ, |lam - 1| ≤ κk → ∀ t, |kLam p lam t - kLam p 1 t| ≤ εk) := by sorry

end LpBallVI.Affine
