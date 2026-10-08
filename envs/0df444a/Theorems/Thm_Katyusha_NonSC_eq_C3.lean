-- Prove2me | Theorems.Thm_Katyusha_NonSC_eq_C3
-- name    : Katyusha.NonSC.eq_C3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T06:58:16.329258+00:00
-- url     : https://prove2.me/theorems/297b01d8-cd0d-4053-baf5-fa474a735a7f
-- title:
--   Inequality (C.3) — the base epoch $s=0$ of Katyusha$^{\mathrm{ns}}$
-- statement:
--   Assume Problem (1.1) with each $f_i$ convex and $L$-smooth ($L>0$), $\psi$ convex, $n\ge1$, $x^*$ a minimizer of $F=f+\psi$, and $m\ge1$. Consider epoch $0$ of Algorithm 2 (Option I), with $\tau_{1,0}=\frac12$, $\tau_2=\frac12$, $\alpha_0=\frac1{3\tau_{1,0}L}$, started from a snapshot $\widetilde x^0$ and a pair $(y_0,z_0)$. With $D_k=F(y_k)-F(x^*)$, $\widetilde D^0=F(\widetilde x^0)-F(x^*)$ and $\mathbb E$ the expectation over the epoch's $m$ independent uniform indices,
--   $$\mathbb E\Big[\frac1{\tau_{1,0}^2}D_m+\frac{\tau_{1,0}+\tau_2}{\tau_{1,0}^2}\sum_{j=1}^{m-1}D_j\Big]\le\frac{1-\tau_{1,0}-\tau_2}{\tau_{1,0}^2}D_0+\frac{\tau_2 m}{\tau_{1,0}^2}\widetilde D^0+\frac{3L}2\|z_0-x^*\|^2-\frac{3L}2\mathbb E\big[\|z_m-x^*\|^2\big].$$
--
--   It is the base case of the telescoping that proves Theorem 4.1.
--
--   **Formalization Note** The start state $(\widetilde x^0,y_0,z_0)$ is arbitrary, as in (C.1), of which this is the case $s=0$ multiplied by $3L$; in the algorithm all three equal $x_0$. The coefficients are written with $\tau_{1,0}$ and $\tau_2$ as in the paper, although $\tau_{1,0}=\tau_2=\frac12$ makes the coefficient of $D_0$ vanish.
-- source:
--   Allen-Zhu, Katyusha: The First Direct Acceleration of Stochastic Gradient Methods, arXiv:1603.05953v6, App. C.1, (C.3), p. 27

import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum
import Definitions.Def_SAGA_Convex_IsProxPoint
import Definitions.Def_SAGA_Convex_sagaRun
import Definitions.Def_Katyusha_NonSC_step
import Definitions.Def_Katyusha_NonSC_run

namespace Katyusha.NonSC

/-- Inequality (C.3) of Allen-Zhu, arXiv:1603.05953v6, App. C.1, p. 27: the base case `s = 0` of
(C.1), multiplied by `3L` (with `α₀ = 1/(3 τ_{1,0} L)`), for the epoch-0 start state
`(x̃⁰, y₀, z₀) = (xt, y0, z0)` (in the algorithm all three equal `x₀`). The expectation is over the
`m` independent uniform indices of epoch 0. -/
theorem eq_C3 {d n m : ℕ} (hn : 0 < n) (hm : 1 ≤ m)
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
    (xt y0 z0 : EuclideanSpace ℝ (Fin d)) :
    SAGA.Convex.expectIdx n m (fun is =>
        1 / tau1 0 ^ 2 * (obj f ψ (epochIter f' P L 0 xt (y0, z0) is m).1 - obj f ψ xstar)
          + (tau1 0 + tau2) / tau1 0 ^ 2 *
            ∑ j ∈ Finset.Ico 1 m, (obj f ψ (epochIter f' P L 0 xt (y0, z0) is j).1 - obj f ψ xstar))
      ≤ (1 - tau1 0 - tau2) / tau1 0 ^ 2 * (obj f ψ y0 - obj f ψ xstar)
        + tau2 * (m : ℝ) / tau1 0 ^ 2 * (obj f ψ xt - obj f ψ xstar)
        + 3 * L / 2 * ‖z0 - xstar‖ ^ 2
        - 3 * L / 2 * SAGA.Convex.expectIdx n m (fun is =>
            ‖(epochIter f' P L 0 xt (y0, z0) is m).2 - xstar‖ ^ 2) := by sorry

end Katyusha.NonSC
