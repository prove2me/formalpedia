-- Prove2me | Theorems.Thm_KatyushaNs_lemma_2_7_coupling_step_2
-- name    : KatyushaNs.lemma_2_7_coupling_step_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:51:43.414907+00:00
-- url     : https://prove2.me/theorems/257227a8-b840-4ae4-b2ef-5ebe06b1801c
-- title:
--   Lemma 2.7: coupling step 2
-- statement:
--   Under the setting of Lemma 2.6 ($f_i$ convex and $L$-smooth, $\psi$ $\sigma$-strongly convex with effective domain $D$, $\alpha > 0$, $0 < \tau_1 \le \frac12$, $\tau_1 \le \frac{1}{3\alpha L}$, $\tau_2 = \frac12$, $\widetilde x, y_k, z_k \in D$, $x_{k+1} = \tau_1 z_k + \tau_2\widetilde x + (1-\tau_1-\tau_2)y_k$, and $z_{k+1}, y_{k+1}$ the two proximal steps for the random estimator), let $x^*$ be a minimizer of $F = f + \psi$. Then
--   $$\begin{aligned}0 \le{}& \frac{\alpha(1-\tau_1-\tau_2)}{\tau_1}\big(F(y_k) - F(x^*)\big) - \frac{\alpha}{\tau_1}\Big(\mathbb{E}\big[F(y_{k+1})\big] - F(x^*)\Big) + \frac{\alpha\tau_2}{\tau_1}\big(F(\widetilde x) - F(x^*)\big)\\ &+ \frac12\|z_k - x^*\|^2 - \frac{1+\alpha\sigma}{2}\mathbb{E}\big[\|z_{k+1} - x^*\|^2\big],\end{aligned}$$
--   with $\mathbb{E}$ the average over the index $i$ uniform in $\{1,\dots,n\}$.
--
--   This one-iteration inequality relates objective gaps to distances to $x^*$; it is the inequality that is telescoped in the proofs of Theorems 2.1 and 4.1.
--
--   Differences from the source:
--   - generalization: ψ convex and lower semicontinuous (Problem (1.1), p. 1) → ψ convex on its effective domain, no lower semicontinuity; reason: lower semicontinuity only guarantees that the arg mins exist; their existence is part of the hypotheses (the prox predicates / the run). Every lsc convex ψ is covered, so the statement specializes to the paper's
--   - encoding: ψ : ℝᵈ → ℝ ∪ {+∞} → a set D (dom ψ) and real values ψ : ℝᵈ → ℝ with ConvexOn ℝ D ψ (or StrongConvexOn), F = f + ψ on D; reason: every convex extended-valued ψ is of this form and conversely; same instances
--   - encoding: ψ σ-SC (Definition 1.2, subgradient form) → StrongConvexOn D σ ψ with σ ≥ 0 (Jensen form, modulus σ/2·r²); reason: for convex functions the two forms agree; σ = 0 is plain convexity
--   - reading: step size α (sign unstated) → α > 0; reason: α is the step size, α_s = 1/(3τ_{1,s}L) > 0 in Algorithms 1 and 2; the arg min of line 11 needs 1/α > 0
--   - reading: τ₁ ≤ 1/(3αL), τ₂ = 1/2 → additionally 0 < τ₁ ≤ 1/2; reason: the paper requires x_{k+1} to be "a convex combination of y_k, z_k and x̃" (p. 10), i.e. 1 − τ₁ − τ₂ ≥ 0, and divides by τ₁; Algorithm 2 has τ_{1,s} = 2/(s+4) ∈ (0, 1/2]
--   - encoding: x̃, y_k, z_k ∈ ℝᵈ → x̃, y_k, z_k ∈ D; reason: off D the paper's ψ is +∞ and the inequality is vacuous or undefined; in the algorithm these points lie in D
--   - encoding: expectation over the index i drawn uniformly from {1, …, n} → the average (1/n) Σ over i : Fin n; reason: the definition of the expectation for the uniform choice of i; index base shifted to Fin n
--   - encoding: n and L implicit (n summands, L-smooth) → 0 < n and 0 < L; reason: n = 0 has no summands and L = 0 makes α_s and 1/(4L) undefined; only undefined cases are excluded
--   - encoding: x* ∈ arg min_x F(x) → x* ∈ D with F(x*) ≤ F(w) for all w ∈ D; reason: F = +∞ off D, so the minimizers of F are exactly these points
-- source:
--   Allen-Zhu, Katyusha: The First Direct Acceleration of Stochastic Gradient Methods, arXiv:1603.05953v6, Lemma 2.7, p. 11

import Mathlib
import Definitions.Def_KatyushaNs_IsConvexLSmooth
import Definitions.Def_KatyushaNs_Fobj
import Definitions.Def_KatyushaNs_svrgEst
import Definitions.Def_KatyushaNs_IsQuadProxMin

namespace KatyushaNs

/-- **Lemma 2.7 (coupling step 2).**
Allen-Zhu, *Katyusha: The First Direct Acceleration of Stochastic Gradient Methods*,
arXiv:1603.05953v6, Lemma 2.7, p. 11 (PDF p. 12): "Under the same choices of τ₁, τ₂ as in
Lemma 2.6, we have
0 ≤ α(1 − τ₁ − τ₂)/τ₁ (F(y_k) − F(x*)) − α/τ₁ (E[F(y_{k+1})] − F(x*)) + ατ₂/τ₁ (F(x̃) − F(x*))
+ 1/2 ‖z_k − x*‖² − (1 + ασ)/2 E[‖z_{k+1} − x*‖²]."

Setting: as in Lemma 2.6 (each `fᵢ` convex and `L`-smooth, `L > 0`; `ψ` `σ`-strongly convex on
its effective domain `D`, `σ ≥ 0`; `α > 0`, `0 < τ₁ ≤ 1/2`, `τ₁ ≤ 1/(3αL)`, `τ₂ = 1/2`;
`xt, yk, zk ∈ D`; `xk1 = τ₁ zk + τ₂ xt + (1 − τ₁ − τ₂) yk`; `zplus i`, `yplus i` the two
proximal steps for the estimator `svrgEst fi xt xk1 i`), and `x* = xstar ∈ D` minimizes
`F = f + ψ` over `D` (Problem (1.1), "x* ∈ arg min_x {F(x)}", p. 1). Conclusion: the displayed
inequality, with `E` the uniform average over the index `i`.

**Formalization Note.** The expectation over the random index is `(1/n) Σᵢ`; `σ`-SC is
`StrongConvexOn D σ ψ`. The conditions `0 < τ₁ ≤ 1/2` are those of Lemma 2.6 (convex combination,
p. 10). `F` is `Fobj fi ψ`; minimizers of the extended-valued `F` are exactly the points of `D`
minimizing `Fobj fi ψ` over `D`. -/
theorem lemma_2_7_coupling_step_2 {d n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    {fi : Fin n → EuclideanSpace ℝ (Fin d) → ℝ} (hfi : ∀ i, IsConvexLSmooth L (fi i))
    {D : Set (EuclideanSpace ℝ (Fin d))} {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    {σ : ℝ} (hσ : 0 ≤ σ) (hψσ : StrongConvexOn D σ ψ)
    {α τ1 : ℝ} (hα : 0 < α) (hτ1 : 0 < τ1) (hτ1h : τ1 ≤ 1 / 2) (hτ1α : τ1 ≤ 1 / (3 * α * L))
    {xt yk zk xk1 : EuclideanSpace ℝ (Fin d)} (hxt : xt ∈ D) (hyk : yk ∈ D) (hzk : zk ∈ D)
    (hxk1 : xk1 = τ1 • zk + (1 / 2 : ℝ) • xt + (1 - τ1 - 1 / 2) • yk)
    {zplus yplus : Fin n → EuclideanSpace ℝ (Fin d)}
    (hz : ∀ i, IsQuadProxMin D ψ α⁻¹ zk (svrgEst fi xt xk1 i) (zplus i))
    (hy : ∀ i, IsQuadProxMin D ψ (3 * L) xk1 (svrgEst fi xt xk1 i) (yplus i))
    {xstar : EuclideanSpace ℝ (Fin d)} (hxs : xstar ∈ D)
    (hmin : ∀ w ∈ D, Fobj fi ψ xstar ≤ Fobj fi ψ w) :
    0 ≤ α * (1 - τ1 - 1 / 2) / τ1 * (Fobj fi ψ yk - Fobj fi ψ xstar) -
        α / τ1 * ((n : ℝ)⁻¹ * ∑ i, Fobj fi ψ (yplus i) - Fobj fi ψ xstar) +
        α * (1 / 2) / τ1 * (Fobj fi ψ xt - Fobj fi ψ xstar) +
        1 / 2 * ‖zk - xstar‖ ^ 2 -
        (1 + α * σ) / 2 * ((n : ℝ)⁻¹ * ∑ i, ‖zplus i - xstar‖ ^ 2) := by sorry

end KatyushaNs
