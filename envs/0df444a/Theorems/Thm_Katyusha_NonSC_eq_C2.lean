-- Prove2me | Theorems.Thm_Katyusha_NonSC_eq_C2
-- name    : Katyusha.NonSC.eq_C2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T06:58:07.984824+00:00
-- url     : https://prove2.me/theorems/bfd4ffc7-2d72-478a-bbd4-25280097adf8
-- title:
--   Inequality (C.2) — the epoch inequality of Katyusha$^{\mathrm{ns}}$ for $s\ge1$
-- statement:
--   Assume Problem (1.1) with each $f_i$ convex and $L$-smooth ($L>0$), $\psi$ convex, $n\ge1$, $x^*$ a minimizer of $F=f+\psi$, and $m\ge1$. Consider an epoch $s\ge1$ of Algorithm 2 (Option I) with $\tau_{1,s}=\frac2{s+4}$, $\tau_2=\frac12$, $\alpha_s=\frac1{3\tau_{1,s}L}$. Let $y_{(s-1)m+1},\dots,y_{(s-1)m+m}$ be the previous epoch's iterates, so that the snapshot is
--   $$\widetilde x^s=\frac1m\sum_{j=1}^m y_{(s-1)m+j}$$
--   and the epoch starts from $y_{sm}=y_{(s-1)m+m}$ and an arbitrary $z_{sm}$. With $D_k=F(y_k)-F(x^*)$ and $\mathbb E$ the expectation over the epoch's $m$ independent uniform indices,
--   $$\mathbb E\Big[\frac1{\tau_{1,s}^2}D_{(s+1)m}+\frac{\tau_{1,s}+\tau_2}{\tau_{1,s}^2}\sum_{j=1}^{m-1}D_{sm+j}\Big]\le\frac{1-\tau_{1,s}}{\tau_{1,s}^2}D_{sm}+\frac{\tau_2}{\tau_{1,s}^2}\sum_{j=1}^{m-1}D_{(s-1)m+j}+\frac{3L}2\|z_{sm}-x^*\|^2-\frac{3L}2\mathbb E\big[\|z_{(s+1)m}-x^*\|^2\big].$$
--
--   It is (C.1) multiplied by $3L$, with the snapshot term bounded through the convexity of $F$; telescoped with (C.3) it yields (C.4).
--
--   **Formalization Note** The previous epoch's iterates are given as a sequence `yp` with `yp j` $=y_{(s-1)m+j}$ ($1\le j\le m$; other values are unused), so the statement needs no conditional expectation. The hypothesis $s\ge1$ is the paper's ("for every $s\ge1$"); the case $s=0$, whose snapshot is $x_0$, is (C.3).
-- source:
--   Allen-Zhu, Katyusha: The First Direct Acceleration of Stochastic Gradient Methods, arXiv:1603.05953v6, App. C.1, (C.2), p. 27 (derived on p. 26)

import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum
import Definitions.Def_SAGA_Convex_IsProxPoint
import Definitions.Def_SAGA_Convex_sagaRun
import Definitions.Def_Katyusha_NonSC_step
import Definitions.Def_Katyusha_NonSC_run

namespace Katyusha.NonSC

/-- Inequality (C.2) of Allen-Zhu, arXiv:1603.05953v6, App. C.1, p. 27, for an epoch `s ≥ 1` of
Algorithm 2: the snapshot is `x̃^s = (1/m) ∑_{j=1}^m y_{(s-1)m+j}`, where `yp j = y_{(s-1)m+j}`
(`1 ≤ j ≤ m`) are the previous epoch's iterates, so that the current `y_{sm} = yp m`, and
`z_{sm} = z0`. The step size is `α_s = 1/(3 τ_{1,s} L)`. The expectation is over epoch `s`'s `m`
independent uniform indices. -/
theorem eq_C2 {d n m : ℕ} (hn : 0 < n) (hm : 1 ≤ m)
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
    (s : ℕ) (hs : 1 ≤ s) (yp : ℕ → EuclideanSpace ℝ (Fin d)) (z0 : EuclideanSpace ℝ (Fin d)) :
    SAGA.Convex.expectIdx n m (fun is =>
        1 / tau1 s ^ 2 * (obj f ψ (epochIter f' P L s ((1 / (m : ℝ)) • ∑ t ∈ Finset.range m, yp (t + 1)) (yp m, z0) is m).1 - obj f ψ xstar)
          + (tau1 s + tau2) / tau1 s ^ 2 *
            ∑ j ∈ Finset.Ico 1 m,
              (obj f ψ (epochIter f' P L s ((1 / (m : ℝ)) • ∑ t ∈ Finset.range m, yp (t + 1)) (yp m, z0) is j).1 - obj f ψ xstar))
      ≤ (1 - tau1 s) / tau1 s ^ 2 * (obj f ψ (yp m) - obj f ψ xstar)
        + tau2 / tau1 s ^ 2 * ∑ j ∈ Finset.Ico 1 m, (obj f ψ (yp j) - obj f ψ xstar)
        + 3 * L / 2 * ‖z0 - xstar‖ ^ 2
        - 3 * L / 2 * SAGA.Convex.expectIdx n m (fun is =>
            ‖(epochIter f' P L s ((1 / (m : ℝ)) • ∑ t ∈ Finset.range m, yp (t + 1)) (yp m, z0) is m).2 - xstar‖ ^ 2) := by sorry

end Katyusha.NonSC
