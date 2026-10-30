-- Prove2me | Theorems.Thm_KatyushaNs_lemma_2_6_coupling_step_1
-- name    : KatyushaNs.lemma_2_6_coupling_step_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:50:59.728246+00:00
-- url     : https://prove2.me/theorems/e5c4b173-7054-40b2-a238-67b24cf40b91
-- title:
--   Lemma 2.6: coupling step 1
-- statement:
--   Let $f_1,\dots,f_n$ ($n \ge 1$) be convex and $L$-smooth with $L > 0$, $f = \frac1n\sum_i f_i$, let $\psi$ be $\sigma$-strongly convex ($\sigma \ge 0$) with effective domain $D$, and $F = f + \psi$. Let $\alpha > 0$, $\tau_2 = \frac12$ and $0 < \tau_1 \le \frac12$ with $\tau_1 \le \frac{1}{3\alpha L}$. Fix $\widetilde x, y_k, z_k \in D$ and
--   $$x_{k+1} = \tau_1 z_k + \tau_2\widetilde x + (1 - \tau_1 - \tau_2) y_k.$$
--   For each index $i$ let $\widetilde\nabla^{(i)} = \nabla f(\widetilde x) + \nabla f_i(x_{k+1}) - \nabla f_i(\widetilde x)$, let $z^{(i)}_{k+1}$ minimize $\frac{1}{2\alpha}\|z - z_k\|^2 + \langle\widetilde\nabla^{(i)}, z\rangle + \psi(z)$ and let $y^{(i)}_{k+1}$ minimize $\frac{3L}{2}\|y - x_{k+1}\|^2 + \langle\widetilde\nabla^{(i)}, y\rangle + \psi(y)$. With $\mathbb{E}$ the average over $i$ uniform in $\{1,\dots,n\}$, for every $u \in D$,
--   $$\begin{aligned}\alpha\langle\nabla f(x_{k+1}), z_k - u\rangle - \alpha\psi(u) \le{}& \frac{\alpha}{\tau_1}\Big(F(x_{k+1}) - \mathbb{E}\big[F(y_{k+1})\big] + \tau_2 F(\widetilde x) - \tau_2 f(x_{k+1}) - \tau_2\langle\nabla f(x_{k+1}), \widetilde x - x_{k+1}\rangle\Big)\\ &+ \frac12\|z_k - u\|^2 - \frac{1+\alpha\sigma}{2}\mathbb{E}\big[\|z_{k+1} - u\|^2\big] + \frac{\alpha(1 - \tau_1 - \tau_2)}{\tau_1}\psi(y_k) - \frac{\alpha}{\tau_1}\psi(x_{k+1}).\end{aligned}$$
--
--   The lemma couples the gradient step (Lemma 2.3), the variance bound (Lemma 2.4) and the mirror step (Lemma 2.5) through the negative momentum $\tau_2\widetilde x$.
--
--   Differences from the source:
--   - generalization: ψ convex and lower semicontinuous (Problem (1.1), p. 1) → ψ convex on its effective domain, no lower semicontinuity; reason: lower semicontinuity only guarantees that the arg mins exist; their existence is part of the hypotheses (the prox predicates / the run). Every lsc convex ψ is covered, so the statement specializes to the paper's
--   - encoding: ψ : ℝᵈ → ℝ ∪ {+∞} → a set D (dom ψ) and real values ψ : ℝᵈ → ℝ with ConvexOn ℝ D ψ (or StrongConvexOn), F = f + ψ on D; reason: every convex extended-valued ψ is of this form and conversely; same instances
--   - encoding: ψ σ-SC (Definition 1.2, subgradient form) → StrongConvexOn D σ ψ with σ ≥ 0 (Jensen form, modulus σ/2·r²); reason: for convex functions the two forms agree; σ = 0 is plain convexity
--   - reading: step size α (sign unstated) → α > 0; reason: α is the step size, α_s = 1/(3τ_{1,s}L) > 0 in Algorithms 1 and 2; the arg min of line 11 needs 1/α > 0
--   - reading: τ₁ ≤ 1/(3αL), τ₂ = 1/2 → additionally 0 < τ₁ ≤ 1/2; reason: the paper requires x_{k+1} to be "a convex combination of y_k, z_k and x̃" (p. 10), i.e. 1 − τ₁ − τ₂ ≥ 0, and divides by τ₁; Algorithm 2 has τ_{1,s} = 2/(s+4) ∈ (0, 1/2]
--   - encoding: x̃, y_k, z_k, u ∈ ℝᵈ → x̃, y_k, z_k, u ∈ D; reason: off D the paper's ψ is +∞ and the inequality is vacuous or undefined; in the algorithm these points lie in D
--   - encoding: expectation over the index i drawn uniformly from {1, …, n} → the average (1/n) Σ over i : Fin n; reason: the definition of the expectation for the uniform choice of i; index base shifted to Fin n
--   - encoding: n and L implicit (n summands, L-smooth) → 0 < n and 0 < L; reason: n = 0 has no summands and L = 0 makes α_s and 1/(4L) undefined; only undefined cases are excluded
-- source:
--   Allen-Zhu, Katyusha: The First Direct Acceleration of Stochastic Gradient Methods, arXiv:1603.05953v6, Lemma 2.6, p. 10

import Mathlib
import Definitions.Def_KatyushaNs_IsConvexLSmooth
import Definitions.Def_KatyushaNs_favg
import Definitions.Def_KatyushaNs_Fobj
import Definitions.Def_KatyushaNs_svrgEst
import Definitions.Def_KatyushaNs_IsQuadProxMin

namespace KatyushaNs

/-- **Lemma 2.6 (coupling step 1).**
Allen-Zhu, *Katyusha: The First Direct Acceleration of Stochastic Gradient Methods*,
arXiv:1603.05953v6, Lemma 2.6, p. 10 (PDF p. 11): "If x_{k+1} = τ₁z_k + τ₂x̃ + (1 − τ₁ − τ₂)y_k,
where τ₁ ≤ 1/(3αL) and τ₂ = 1/2,
α⟨∇f(x_{k+1}), z_k − u⟩ − αψ(u)
≤ α/τ₁ ( F(x_{k+1}) − E[F(y_{k+1})] + τ₂F(x̃) − τ₂f(x_{k+1}) − τ₂⟨∇f(x_{k+1}), x̃ − x_{k+1}⟩ )
+ 1/2 ‖z_k − u‖² − (1 + ασ)/2 E[‖z_{k+1} − u‖²] + α(1 − τ₁ − τ₂)/τ₁ ψ(y_k) − α/τ₁ ψ(x_{k+1})."

Setting (§2.1, pp. 8–10): each `fᵢ` convex and `L`-smooth, `L > 0`; `ψ` is `σ`-strongly convex
(`σ ≥ 0`) on its effective domain `D`; `α > 0`; `0 < τ₁ ≤ 1/2` and `τ₁ ≤ 1/(3αL)`; `τ₂ = 1/2`;
the snapshot `xt = x̃`, `yk`, `zk` lie in `D` and are fixed;
`xk1 = x_{k+1} = τ₁ zk + τ₂ xt + (1 − τ₁ − τ₂) yk`. For each index `i`, the estimator is
`∇̃(i) = svrgEst fi xt xk1 i`, `zplus i = z_{k+1}` minimizes
`z ↦ (1/(2α))‖z − zk‖² + ⟨∇̃(i), z⟩ + ψ(z)` and `yplus i = y_{k+1}` minimizes
`y ↦ (3L/2)‖y − xk1‖² + ⟨∇̃(i), y⟩ + ψ(y)` (Algorithm 1/2 lines for `z` and `y`, Option I).
Conclusion: the displayed inequality for every `u ∈ D`, with `E` the uniform average over `i`.

**Formalization Note.** The expectation over the random index is `(1/n) Σᵢ`. `σ`-SC is
`StrongConvexOn D σ ψ`. The condition `0 < τ₁ ≤ 1/2` comes from the paper's requirement that
`x_{k+1}` be "a convex combination of y_k, z_k and x̃" (p. 10) with `τ₂ = 1/2`, and from the
division by `τ₁`. The points `xt, yk, zk, u` are taken in `D` (off `D` the paper's `ψ` is `+∞`). -/
theorem lemma_2_6_coupling_step_1 {d n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    {fi : Fin n → EuclideanSpace ℝ (Fin d) → ℝ} (hfi : ∀ i, IsConvexLSmooth L (fi i))
    {D : Set (EuclideanSpace ℝ (Fin d))} {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    {σ : ℝ} (hσ : 0 ≤ σ) (hψσ : StrongConvexOn D σ ψ)
    {α τ1 : ℝ} (hα : 0 < α) (hτ1 : 0 < τ1) (hτ1h : τ1 ≤ 1 / 2) (hτ1α : τ1 ≤ 1 / (3 * α * L))
    {xt yk zk xk1 : EuclideanSpace ℝ (Fin d)} (hxt : xt ∈ D) (hyk : yk ∈ D) (hzk : zk ∈ D)
    (hxk1 : xk1 = τ1 • zk + (1 / 2 : ℝ) • xt + (1 - τ1 - 1 / 2) • yk)
    {zplus yplus : Fin n → EuclideanSpace ℝ (Fin d)}
    (hz : ∀ i, IsQuadProxMin D ψ α⁻¹ zk (svrgEst fi xt xk1 i) (zplus i))
    (hy : ∀ i, IsQuadProxMin D ψ (3 * L) xk1 (svrgEst fi xt xk1 i) (yplus i)) :
    ∀ u ∈ D,
      α * inner ℝ (gradient (favg fi) xk1) (zk - u) - α * ψ u ≤
        α / τ1 * (Fobj fi ψ xk1 - (n : ℝ)⁻¹ * ∑ i, Fobj fi ψ (yplus i) +
            1 / 2 * Fobj fi ψ xt - 1 / 2 * favg fi xk1 -
            1 / 2 * inner ℝ (gradient (favg fi) xk1) (xt - xk1)) +
          1 / 2 * ‖zk - u‖ ^ 2 -
          (1 + α * σ) / 2 * ((n : ℝ)⁻¹ * ∑ i, ‖zplus i - u‖ ^ 2) +
          α * (1 - τ1 - 1 / 2) / τ1 * ψ yk - α / τ1 * ψ xk1 := by sorry

end KatyushaNs
