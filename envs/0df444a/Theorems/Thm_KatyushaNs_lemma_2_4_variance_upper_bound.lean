-- Prove2me | Theorems.Thm_KatyushaNs_lemma_2_4_variance_upper_bound
-- name    : KatyushaNs.lemma_2_4_variance_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:49:56.935983+00:00
-- url     : https://prove2.me/theorems/b770c9bb-af4c-4e7c-8c76-9b70fd2e6eca
-- title:
--   Lemma 2.4: variance upper bound
-- statement:
--   Let $f_1,\dots,f_n : \mathbb{R}^d \to \mathbb{R}$ be convex and $L$-smooth and $f = \frac1n\sum_i f_i$. For any snapshot $\widetilde x$ and point $x_{k+1}$, let $\widetilde\nabla_{k+1} = \nabla f(\widetilde x) + \nabla f_i(x_{k+1}) - \nabla f_i(\widetilde x)$ with $i$ uniform in $\{1,\dots,n\}$. Then
--   $$\mathbb{E}\big[\|\widetilde\nabla_{k+1} - \nabla f(x_{k+1})\|^2\big] \le 2L\cdot\Big(f(\widetilde x) - f(x_{k+1}) - \langle \nabla f(x_{k+1}), \widetilde x - x_{k+1}\rangle\Big).$$
--
--   The variance of the SVRG estimator is controlled by the Bregman divergence of $f$ between $\widetilde x$ and $x_{k+1}$, a quantity that the Katyusha momentum later cancels.
--
--   Differences from the source:
--   - encoding: expectation over the index i drawn uniformly from {1, …, n} → the average (1/n) Σ over i : Fin n; reason: the definition of the expectation for the uniform choice of i; index base shifted to Fin n
-- source:
--   Allen-Zhu, Katyusha: The First Direct Acceleration of Stochastic Gradient Methods, arXiv:1603.05953v6, Lemma 2.4, p. 9

import Mathlib
import Definitions.Def_KatyushaNs_IsConvexLSmooth
import Definitions.Def_KatyushaNs_favg
import Definitions.Def_KatyushaNs_svrgEst

namespace KatyushaNs

/-- **Lemma 2.4 (variance upper bound).**
Allen-Zhu, *Katyusha: The First Direct Acceleration of Stochastic Gradient Methods*,
arXiv:1603.05953v6, Lemma 2.4, p. 9 (PDF p. 10):
"E[‖∇̃_{k+1} − ∇f(x_{k+1})‖²] ≤ 2L · (f(x̃) − f(x_{k+1}) − ⟨∇f(x_{k+1}), x̃ − x_{k+1}⟩)."

Setting: each `fᵢ` convex and `L`-smooth; `xt = x̃` (the snapshot) and `x = x_{k+1}` are any two
points; `∇̃_{k+1} = svrgEst fi xt x i` with `i` uniform on the `n` indices. Conclusion:
`(1/n) Σᵢ ‖∇̃(i) − ∇f(x)‖² ≤ 2L (f(xt) − f(x) − ⟨∇f(x), xt − x⟩)`.

**Formalization Note.** The expectation over the random index is `(1/n) Σᵢ`. No assumption on
`n` or on `L` is added: the paper states none for this lemma, and at `n = 0` both sides are `0`. -/
theorem lemma_2_4_variance_upper_bound {d n : ℕ} {L : ℝ}
    {fi : Fin n → EuclideanSpace ℝ (Fin d) → ℝ} (hfi : ∀ i, IsConvexLSmooth L (fi i))
    (xt x : EuclideanSpace ℝ (Fin d)) :
    (n : ℝ)⁻¹ * ∑ i, ‖svrgEst fi xt x i - gradient (favg fi) x‖ ^ 2 ≤
      2 * L * (favg fi xt - favg fi x - inner ℝ (gradient (favg fi) x) (xt - x)) := by sorry

end KatyushaNs
