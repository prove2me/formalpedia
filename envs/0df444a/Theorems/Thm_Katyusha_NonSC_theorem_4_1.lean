-- Prove2me | Theorems.Thm_Katyusha_NonSC_theorem_4_1
-- name    : Katyusha.NonSC.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T06:58:33.950958+00:00
-- url     : https://prove2.me/theorems/b034dfdf-ffc1-4118-a532-4b709c7fb35c
-- title:
--   Theorem 4.1 — Katyusha$^{\mathrm{ns}}$ reaches $\mathbb E[F(\widetilde x^S)]-F(x^*)\le\frac{16(F(x_0)-F(x^*))}{(S+3)^2}+\frac{12L\|x_0-x^*\|^2}{m(S+3)^2}$
-- statement:
--   Consider the composite finite-sum problem (1.1): minimize
--   $$F(x)=f(x)+\psi(x)=\frac1n\sum_{i=1}^n f_i(x)+\psi(x),\qquad x\in\mathbb R^d,$$
--   with $n\ge1$, each $f_i$ convex and $L$-smooth ($\|\nabla f_i(x)-\nabla f_i(y)\|\le L\|x-y\|$, $L>0$), and $\psi$ convex but not necessarily strongly convex. Let $x^*$ be a minimizer of $F$.
--
--   Run Algorithm 2, $\mathtt{Katyusha}^{\mathrm{ns}}(x_0,S,L)$ with Option I and epoch length $m\ge1$: with $\tau_2=\frac12$ and $y_0=z_0=\widetilde x^0=x_0$, epoch $s=0,\dots,S-1$ uses $\tau_{1,s}=\frac2{s+4}$ and $\alpha_s=\frac1{3\tau_{1,s}L}$ and performs $m$ iterations $k=sm+j$:
--   $$x_{k+1}=\tau_{1,s}z_k+\tau_2\widetilde x^s+(1-\tau_{1,s}-\tau_2)y_k,\qquad \widetilde\nabla_{k+1}=\nabla f(\widetilde x^s)+\nabla f_i(x_{k+1})-\nabla f_i(\widetilde x^s),$$
--   $$z_{k+1}=\arg\min_z\Big\{\tfrac1{2\alpha_s}\|z-z_k\|^2+\langle\widetilde\nabla_{k+1},z\rangle+\psi(z)\Big\},\qquad y_{k+1}=\arg\min_y\Big\{\tfrac{3L}2\|y-x_{k+1}\|^2+\langle\widetilde\nabla_{k+1},y\rangle+\psi(y)\Big\},$$
--   where $i$ is drawn uniformly from $\{1,\dots,n\}$, independently in every iteration; then $\widetilde x^{s+1}=\frac1m\sum_{j=1}^m y_{sm+j}$. The output is $\widetilde x^S$. Then for every $S\ge0$,
--   $$\mathbb E\big[F(\widetilde x^S)\big]-F(x^*)\le\frac{16\,\big(F(x_0)-F(x^*)\big)}{(S+3)^2}+\frac{12\,L\,\|x_0-x^*\|^2}{m\,(S+3)^2}.$$
--
--   The paper states the bound as $O\big(\frac{F(x_0)-F(x^*)}{S^2}+\frac{L\|x_0-x^*\|^2}{mS^2}\big)$; its proof (App. C.1) yields the constants $16$ and $12$ above. This is the accelerated $O(1/S^2)$ rate for the non-strongly convex case, a factor $S$ faster than non-accelerated variance-reduced methods such as SAGA.
--
--   **Formalization Note** The paper writes $O(\cdot)$; the proof yields $\frac{2\tau_{1,S-1}^2}{m}\big(2mD_0+\frac{3L}2\|x_0-x^*\|^2\big)$ with $\tau_{1,S-1}=\frac2{S+3}$, which is the right-hand side above (at $S=0$ the bound holds trivially). The epoch length $m\ge1$ is a parameter (the algorithm sets $m=2n$); the algorithm's unused input $\sigma$ and Option II are not modelled, and the "in other words" iteration count is not part of this statement. The two arg-min steps are evaluated by a map $P$ assumed to return proximal points of $\psi$ (`SAGA.Convex.IsProxPoint`); the gradients are tied to the $f_i$ by `HasGradientAt`; $\psi$ is real-valued. The expectation is the uniform average over all $n^{Sm}$ index sequences.
-- source:
--   Allen-Zhu, Katyusha: The First Direct Acceleration of Stochastic Gradient Methods, arXiv:1603.05953v6, p. 15, Theorem 4.1 (Algorithm 2, p. 15; proof in App. C.1, pp. 26–27)

import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum
import Definitions.Def_SAGA_Convex_IsProxPoint
import Definitions.Def_SAGA_Convex_sagaRun
import Definitions.Def_Katyusha_NonSC_step
import Definitions.Def_Katyusha_NonSC_run

namespace Katyusha.NonSC

/-- Theorem 4.1 of Allen-Zhu, arXiv:1603.05953v6, p. 15 (proof in App. C.1, pp. 26–27), with the
explicit constants of its proof: if each `fᵢ` is convex and `L`-smooth and `ψ` is convex (not
necessarily strongly convex), then the output `x̃^S` of `Katyusha^ns(x₀, S, L)` (Algorithm 2,
Option I, epoch length `m ≥ 1`) satisfies
`E[F(x̃^S)] - F(x*) ≤ 16 (F(x₀) - F(x*))/(S+3)² + 12 L ‖x₀ - x*‖²/(m (S+3)²)`,
the expectation being over the `S m` independent uniform indices. The paper writes
`O((F(x₀) - F(x*))/S² + L ‖x₀ - x*‖²/(m S²))`. -/
theorem theorem_4_1 {d n m : ℕ} (hn : 0 < n) (hm : 1 ≤ m)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ) (hL : 0 < L)
    (hf_grad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hf_conv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (hf_smooth : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (hψ : ConvexOn ℝ Set.univ ψ)
    (P : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hP : ∀ γ : ℝ, 0 < γ → ∀ v, SAGA.Convex.IsProxPoint ψ γ v (P γ v))
    (xstar : EuclideanSpace ℝ (Fin d)) (hxstar : ∀ x, obj f ψ xstar ≤ obj f ψ x)
    (x0 : EuclideanSpace ℝ (Fin d)) (S : ℕ) :
    SAGA.Convex.expectIdx n (S * m)
        (fun js => obj f ψ (output f' P L x0 (blocks (S := S) (m := m) js)))
        - obj f ψ xstar
      ≤ 16 * (obj f ψ x0 - obj f ψ xstar) / ((S : ℝ) + 3) ^ 2
        + 12 * L * ‖x0 - xstar‖ ^ 2 / ((m : ℝ) * ((S : ℝ) + 3) ^ 2) := by sorry

end Katyusha.NonSC
