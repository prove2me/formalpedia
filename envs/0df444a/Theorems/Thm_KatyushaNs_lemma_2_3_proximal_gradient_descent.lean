-- Prove2me | Theorems.Thm_KatyushaNs_lemma_2_3_proximal_gradient_descent
-- name    : KatyushaNs.lemma_2_3_proximal_gradient_descent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:49:15.269993+00:00
-- url     : https://prove2.me/theorems/5443080b-67be-42ad-a1fc-5b51a3268d19
-- title:
--   Lemma 2.3: proximal gradient descent
-- statement:
--   Let $f_1,\dots,f_n : \mathbb{R}^d \to \mathbb{R}$ ($n \ge 1$) be convex and $L$-smooth with $L > 0$, $f = \frac1n\sum_i f_i$, and let $\psi$ be convex with effective domain $D$; $F = f + \psi$. Fix a snapshot $\widetilde x$ and a point $x_{k+1} \in D$. For each index $i$ let $\widetilde\nabla^{(i)} = \nabla f(\widetilde x) + \nabla f_i(x_{k+1}) - \nabla f_i(\widetilde x)$ and let
--   $$y^{(i)}_{k+1} \in \operatorname*{arg\,min}_y \Big\{ \frac{3L}{2}\|y - x_{k+1}\|^2 + \langle \widetilde\nabla^{(i)}, y - x_{k+1}\rangle + \psi(y) - \psi(x_{k+1}) \Big\}.$$
--   Define
--   $$\mathrm{Prog}^{(i)}(x_{k+1}) = -\min_y \Big\{ \frac{3L}{2}\|y - x_{k+1}\|^2 + \langle \widetilde\nabla^{(i)}, y - x_{k+1}\rangle + \psi(y) - \psi(x_{k+1}) \Big\}$$
--   (the minimum is attained at $y^{(i)}_{k+1}$) and $\sigma^{2,(i)}_{k+1} = \|\nabla f(x_{k+1}) - \widetilde\nabla^{(i)}\|^2$. Then
--
--   1. $\mathrm{Prog}^{(i)}(x_{k+1}) \ge 0$ for every $i$;
--   2. with $\mathbb{E}$ the average over $i$ uniform in $\{1,\dots,n\}$,
--   $$F(x_{k+1}) - \mathbb{E}\big[F(y_{k+1})\big] \ge \mathbb{E}\big[\mathrm{Prog}(x_{k+1})\big] - \frac{1}{4L}\,\mathbb{E}\big[\sigma^2_{k+1}\big].$$
--
--   The lemma lower-bounds the expected decrease of the objective in one gradient step by the classical progress term minus a variance penalty.
--
--   Differences from the source:
--   - generalization: ψ convex and lower semicontinuous (Problem (1.1), p. 1) → ψ convex on its effective domain, no lower semicontinuity; reason: lower semicontinuity only guarantees that the arg mins exist; their existence is part of the hypotheses (the prox predicates / the run). Every lsc convex ψ is covered, so the statement specializes to the paper's
--   - encoding: ψ : ℝᵈ → ℝ ∪ {+∞} → a set D (dom ψ) and real values ψ : ℝᵈ → ℝ with ConvexOn ℝ D ψ (or StrongConvexOn), F = f + ψ on D; reason: every convex extended-valued ψ is of this form and conversely; same instances
--   - encoding: x_{k+1} ∈ ℝᵈ → x_{k+1} ∈ D; reason: F(x_{k+1}) and ψ(x_{k+1}) are +∞ off D; in the algorithm x_{k+1} lies in D
--   - encoding: expectation over the index i drawn uniformly from {1, …, n} → the average (1/n) Σ over i : Fin n; reason: the definition of the expectation for the uniform choice of i; index base shifted to Fin n
--   - encoding: n and L implicit (n summands, L-smooth) → 0 < n and 0 < L; reason: n = 0 has no summands and L = 0 makes α_s and 1/(4L) undefined; only undefined cases are excluded
--   - reading: "Prog(x_{k+1}) def= −min{…} ≥ 0" in the hypotheses → Prog ≥ 0 stated as a conclusion, Prog written as minus the objective at the minimizer y_{k+1}; reason: the inequality ≥ 0 is part of the definition sentence and holds because y = x_{k+1} is feasible; proving it is not weaker than assuming it, and the minimum is attained at the arg min y_{k+1}
-- source:
--   Allen-Zhu, Katyusha: The First Direct Acceleration of Stochastic Gradient Methods, arXiv:1603.05953v6, Lemma 2.3, p. 8

import Mathlib
import Definitions.Def_KatyushaNs_IsConvexLSmooth
import Definitions.Def_KatyushaNs_favg
import Definitions.Def_KatyushaNs_Fobj
import Definitions.Def_KatyushaNs_svrgEst
import Definitions.Def_KatyushaNs_IsQuadProxMin

namespace KatyushaNs

/-- **Lemma 2.3 (proximal gradient descent).**
Allen-Zhu, *Katyusha: The First Direct Acceleration of Stochastic Gradient Methods*,
arXiv:1603.05953v6, Lemma 2.3, p. 8 (PDF p. 9): "If
y_{k+1} = arg min_y { 3L/2 ‖y − x_{k+1}‖² + ⟨∇̃_{k+1}, y − x_{k+1}⟩ + ψ(y) − ψ(x_{k+1}) }, and
Prog(x_{k+1}) def= − min_y { 3L/2 ‖y − x_{k+1}‖² + ⟨∇̃_{k+1}, y − x_{k+1}⟩ + ψ(y) − ψ(x_{k+1}) } ≥ 0,
we have (where the expectation is only over the randomness of ∇̃_{k+1})
F(x_{k+1}) − E[F(y_{k+1})] ≥ E[Prog(x_{k+1})] − 1/(4L) E[σ²_{k+1}]."
Here (§2.1, p. 8) `σ²_{k+1} = ‖∇f(x_{k+1}) − ∇̃_{k+1}‖²`.

Setting: each `fᵢ` convex and `L`-smooth, `L > 0`; `ψ` convex with effective domain `D`;
`x = x_{k+1} ∈ D`; for each index `i`, `svrgEst fi xt x i` is the estimator `∇̃_{k+1}` when `i`
is drawn, and `yplus i ∈ D` is the arg min above for that estimator.
Conclusions: (1) for each `i`, `Prog(x)` (the negated minimum value, attained at `yplus i`) is
`≥ 0`; (2) `E[Prog] − E[σ²]/(4L) ≤ F(x) − E[F(y_{k+1})]`, with `E` the uniform average over `i`.

**Formalization Note.** The expectation over the random index is `(1/n) Σᵢ`. The arg min is the
predicate `IsQuadProxMin D ψ (3L) x (∇̃(i)) (yplus i)`; the paper's objective differs from it by
the constant `−⟨∇̃(i), x⟩ − ψ(x)`, which does not change the minimizer, and the minimum value is
the objective at `yplus i`. -/
theorem lemma_2_3_proximal_gradient_descent {d n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    {fi : Fin n → EuclideanSpace ℝ (Fin d) → ℝ} (hfi : ∀ i, IsConvexLSmooth L (fi i))
    {D : Set (EuclideanSpace ℝ (Fin d))} {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hψ : ConvexOn ℝ D ψ) {xt x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ D)
    {yplus : Fin n → EuclideanSpace ℝ (Fin d)}
    (hy : ∀ i, IsQuadProxMin D ψ (3 * L) x (svrgEst fi xt x i) (yplus i)) :
    (∀ i, 0 ≤ -(3 * L / 2 * ‖yplus i - x‖ ^ 2 + inner ℝ (svrgEst fi xt x i) (yplus i - x) +
        ψ (yplus i) - ψ x)) ∧
      (n : ℝ)⁻¹ * ∑ i, -(3 * L / 2 * ‖yplus i - x‖ ^ 2 +
          inner ℝ (svrgEst fi xt x i) (yplus i - x) + ψ (yplus i) - ψ x) -
        1 / (4 * L) * ((n : ℝ)⁻¹ * ∑ i, ‖gradient (favg fi) x - svrgEst fi xt x i‖ ^ 2) ≤
      Fobj fi ψ x - (n : ℝ)⁻¹ * ∑ i, Fobj fi ψ (yplus i) := by sorry

end KatyushaNs
