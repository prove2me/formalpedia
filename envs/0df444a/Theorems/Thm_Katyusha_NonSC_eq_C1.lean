-- Prove2me | Theorems.Thm_Katyusha_NonSC_eq_C1
-- name    : Katyusha.NonSC.eq_C1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T06:57:57.242377+00:00
-- url     : https://prove2.me/theorems/eddae6c9-5d04-4a21-ac3c-801e9b43b7e4
-- title:
--   Inequality (C.1) — Lemma 2.7 summed over one epoch of Katyusha$^{\mathrm{ns}}$
-- statement:
--   Assume Problem (1.1) with each $f_i$ convex and $L$-smooth ($L>0$), $\psi$ convex, $n\ge1$, and $x^*$ a minimizer of $F=f+\psi$. Let $m\ge1$ and consider epoch $s\ge0$ of Algorithm 2 ($\mathtt{Katyusha}^{\mathrm{ns}}$, Option I) with parameters $\tau_{1,s}=\frac2{s+4}$, $\tau_2=\frac12$, $\alpha_s=\frac1{3\tau_{1,s}L}$, started from an arbitrary snapshot $\widetilde x^s$ and pair $(y_{sm},z_{sm})$. Write $D_k=F(y_k)-F(x^*)$ and $\widetilde D^s=F(\widetilde x^s)-F(x^*)$. Then, with $\mathbb E$ the expectation over the $m$ independent uniform indices of the epoch,
--   $$\mathbb E\Big[\alpha_s\frac{1-\tau_{1,s}-\tau_2}{\tau_{1,s}}D_{(s+1)m}+\alpha_s\frac{\tau_{1,s}+\tau_2}{\tau_{1,s}}\sum_{j=1}^m D_{sm+j}\Big]\le\alpha_s\frac{1-\tau_{1,s}-\tau_2}{\tau_{1,s}}D_{sm}+\alpha_s\frac{\tau_2}{\tau_{1,s}}\,m\,\widetilde D^s+\frac12\|z_{sm}-x^*\|^2-\frac12\mathbb E\big[\|z_{(s+1)m}-x^*\|^2\big].$$
--
--   The start state of the epoch is arbitrary: this is the paper's convention that "all the randomness in the first $s-1$ epochs are fixed and the only source of randomness comes from epoch $s$". The inequality is the per-epoch building block of the proof of Theorem 4.1.
--
--   **Formalization Note** The epoch's iterates are `epochIter` with the epoch's index block `Fin m → Fin n`; the expectation is the uniform average over all $n^m$ blocks (`SAGA.Convex.expectIdx`). Prox points and gradients are tied to $\psi$ and $f_i$ by hypotheses, as in Lemma 2.7.
-- source:
--   Allen-Zhu, Katyusha: The First Direct Acceleration of Stochastic Gradient Methods, arXiv:1603.05953v6, App. C.1, (C.1), p. 26

import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum
import Definitions.Def_SAGA_Convex_IsProxPoint
import Definitions.Def_SAGA_Convex_sagaRun
import Definitions.Def_Katyusha_NonSC_step
import Definitions.Def_Katyusha_NonSC_run

namespace Katyusha.NonSC

/-- Inequality (C.1) of Allen-Zhu, arXiv:1603.05953v6, App. C.1, p. 26: Lemma 2.7 (with `σ = 0`)
summed over the `m` iterations `k = sm, …, sm + m - 1` of epoch `s` of Algorithm 2, from any epoch
start state `(x̃^s, y_{sm}, z_{sm}) = (xt, y0, z0)`. The expectation is over the epoch's `m`
independent uniform indices, the earlier randomness being fixed. -/
theorem eq_C1 {d n m : ℕ} (hn : 0 < n) (hm : 1 ≤ m)
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
    (s : ℕ) (xt y0 z0 : EuclideanSpace ℝ (Fin d)) :
    SAGA.Convex.expectIdx n m (fun is =>
        alpha L s * (1 - tau1 s - tau2) / tau1 s *
            (obj f ψ (epochIter f' P L s xt (y0, z0) is m).1 - obj f ψ xstar)
          + alpha L s * (tau1 s + tau2) / tau1 s *
            ∑ j ∈ Finset.Icc 1 m, (obj f ψ (epochIter f' P L s xt (y0, z0) is j).1 - obj f ψ xstar))
      ≤ alpha L s * (1 - tau1 s - tau2) / tau1 s * (obj f ψ y0 - obj f ψ xstar)
        + alpha L s * tau2 / tau1 s * (m : ℝ) * (obj f ψ xt - obj f ψ xstar)
        + 1 / 2 * ‖z0 - xstar‖ ^ 2
        - 1 / 2 * SAGA.Convex.expectIdx n m (fun is =>
            ‖(epochIter f' P L s xt (y0, z0) is m).2 - xstar‖ ^ 2) := by sorry

end Katyusha.NonSC
