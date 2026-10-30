-- Prove2me | Theorems.Thm_KatyushaNs_eq_C4_telescoped
-- name    : KatyushaNs.eq_C4_telescoped
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:55:36.050084+00:00
-- url     : https://prove2.me/theorems/5a3f21bc-87c5-4750-90d5-d21ce0cec3a5
-- title:
--   Eq. (C.4): the telescoped bound after $S$ epochs
-- statement:
--   Let $f_1,\dots,f_n : \mathbb{R}^d \to \mathbb{R}$ ($n \ge 1$) be convex and $L$-smooth with $L > 0$, $f = \frac1n\sum_i f_i$, let $\psi$ be convex with effective domain $D$ (possibly $+\infty$ off $D$, not necessarily strongly convex), $F = f + \psi$, $x_0 \in D$, and let $x^* \in D$ minimize $F$. Run Katyusha$^{\mathrm{ns}}$ (Algorithm 2, Option I, $m = 2n$, $\tau_2 = \frac12$, $\tau_{1,s} = \frac{2}{s+4}$, $\alpha_s = \frac{1}{3\tau_{1,s}L}$) from $x_0$ with independent uniform indices, and write $D_k = F(y_k) - F(x^*)$, $\widetilde D^s = F(\widetilde x^s) - F(x^*)$.
--
--   For every $S \ge 1$,
--   $$\begin{aligned}&\mathbb{E}\Big[\frac{1}{\tau_{1,S-1}^2}D_{Sm} + \frac{\tau_{1,S-1}+\tau_2}{\tau_{1,S-1}^2}\sum_{j=1}^{m-1}D_{(S-1)m+j} + \frac{3L}{2}\|z_{Sm} - x^*\|^2\Big]\\ &\le \frac{1-\tau_{1,0}-\tau_2}{\tau_{1,0}^2}\big(F(x_0) - F(x^*)\big) + \frac{\tau_2 m}{\tau_{1,0}^2}\big(F(x_0) - F(x^*)\big) + \frac{3L}{2}\|x_0 - x^*\|^2,\end{aligned}$$
--   where $\mathbb{E}$ averages over the indices of the first $Sm$ iterations.
--
--   This is (C.3) and (C.2) chained over $s = 0, \dots, S-1$ with the inequalities of the schedule $\tau_{1,s}$; Theorem 4.1 follows from it.
--
--   Differences from the source:
--   - generalization: ψ convex and lower semicontinuous (Problem (1.1), p. 1) → ψ convex on its effective domain, no lower semicontinuity; reason: lower semicontinuity only guarantees that the arg mins exist; their existence is part of the hypotheses (the prox predicates / the run). Every lsc convex ψ is covered, so the statement specializes to the paper's
--   - encoding: ψ : ℝᵈ → ℝ ∪ {+∞} → a set D (dom ψ) and real values ψ : ℝᵈ → ℝ with ConvexOn ℝ D ψ (or StrongConvexOn), F = f + ψ on D; reason: every convex extended-valued ψ is of this form and conversely; same instances
--   - encoding: arbitrary starting point x₀ → x₀ ∈ D; reason: for x₀ ∉ dom ψ the paper's right side F(x₀) − F(x*) is +∞ and the claim is vacuous
--   - encoding: x* ∈ arg min_x F(x) → x* ∈ D with F(x*) ≤ F(w) for all w ∈ D; reason: F = +∞ off D, so the minimizers of F are exactly these points
--   - reading: Algorithm 2 with Option I or Option II → Option I only (line 12); reason: the paper states "we analyze only I" (Algorithm 2, line 13)
--   - encoding: n and L implicit (n summands, L-smooth) → 0 < n and 0 < L; reason: n = 0 has no summands and L = 0 makes α_s and 1/(4L) undefined; only undefined cases are excluded
--   - encoding: E[·] over the random indices → seqAvg hn N: the uniform average over all index sequences of the first N iterations; reason: the definition of the expectation for independent uniform indices; the averaged quantities depend only on those indices
--   - encoding: the random iterates of Katyusha^ns(x₀, S, L) run for S epochs → functions x, y, z, x̃ of the whole index sequence ω (ℕ → Fin n) satisfying lines 3, 9, 11, 12 (Option I) and 15 for every epoch s (IsKatyushaNsRun); reason: the arg mins are unique (strongly convex objectives on the convex set D), so the iterates are determined by ω, iterate k depends only on ω 0, …, ω (k − 1), and the first S epochs do not depend on the input S (τ_{1,s}, α_s depend on s only); for the paper's lsc ψ every arg min exists, so such a run exists for every ω
--   - reading: ‖z_{Sm} − z*‖² (printed) → ‖z_{Sm} − x*‖²; reason: the paper defines no z*; (C.2) and (C.3), which are telescoped, have ‖z − x*‖²
--   - encoding: D_0, D̃⁰ and ‖z_0 − x*‖² on the right → F(x₀) − F(x*), F(x₀) − F(x*) and ‖x₀ − x*‖²; reason: y_0 = z_0 = x̃⁰ = x₀ by line 3 of Algorithm 2
-- source:
--   Allen-Zhu, Katyusha: The First Direct Acceleration of Stochastic Gradient Methods, arXiv:1603.05953v6, proof of Theorem 4.1 (App. C.1), eq. (C.4), p. 27

import Mathlib
import Definitions.Def_KatyushaNs_IsConvexLSmooth
import Definitions.Def_KatyushaNs_Fobj
import Definitions.Def_KatyushaNs_tau1
import Definitions.Def_KatyushaNs_IsKatyushaNsRun
import Definitions.Def_KatyushaNs_seqAvg

namespace KatyushaNs

/-- **Eq. (C.4): (C.3) and (C.2) telescoped over `s = 0, …, S − 1`.**
Allen-Zhu, *Katyusha: The First Direct Acceleration of Stochastic Gradient Methods*,
arXiv:1603.05953v6, proof of Theorem 4.1 (App. C.1), eq. (C.4), p. 27 (PDF p. 28): "Using these
two inequalities, we can telescope (C.3) and (C.2) for all s = 0, 1, …, S − 1. We obtain in the
end that
E[ 1/τ²_{1,S−1} D_{Sm} + (τ_{1,S−1} + τ₂)/τ²_{1,S−1} Σ_{j=1}^{m−1} D_{(S−1)m+j} + 3L/2 ‖z_{Sm} − z*‖² ]
≤ (1 − τ_{1,0} − τ₂)/τ²_{1,0} D_0 + τ₂m/τ²_{1,0} D̃⁰ + 3L/2 ‖z_0 − x*‖² (C.4)"
Here `D_k = F(y_k) − F(x*)`, `D̃⁰ = F(x̃⁰) − F(x*)`.

Setting: as in Theorem 4.1 (each `fᵢ` convex and `L`-smooth, `n ≥ 1`, `L > 0`; `ψ` convex on its
effective domain `D`; `x₀ ∈ D`; `x* ∈ D` a minimizer of `F`; a run of Katyusha^ns, Option I,
`m = 2n`, `τ₂ = 1/2`). Conclusion: for every `S ≥ 1`, (C.4) with `E` the average over the indices
of the first `S·m` iterations.

**Formalization Note.** `E` is `seqAvg hn (S·m)`. The printed `‖z_{Sm} − z*‖²` is read as
`‖z_{Sm} − x*‖²` (there is no `z*` in the paper; (C.2) and (C.3) have `x*`). By line 3 of
Algorithm 2, `y_0 = z_0 = x̃⁰ = x₀`, so `D_0 = D̃⁰ = F(x₀) − F(x*)` and `z_0 = x₀`; the right side is
written with `x₀`. `S − 1` is natural-number subtraction with `S ≥ 1`. -/
theorem eq_C4_telescoped {d n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    {fi : Fin n → EuclideanSpace ℝ (Fin d) → ℝ} (hfi : ∀ i, IsConvexLSmooth L (fi i))
    {D : Set (EuclideanSpace ℝ (Fin d))} {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hψ : ConvexOn ℝ D ψ) {x0 : EuclideanSpace ℝ (Fin d)} (hx0 : x0 ∈ D)
    {xstar : EuclideanSpace ℝ (Fin d)} (hxs : xstar ∈ D)
    (hmin : ∀ w ∈ D, Fobj fi ψ xstar ≤ Fobj fi ψ w)
    {x y z xt : (ℕ → Fin n) → ℕ → EuclideanSpace ℝ (Fin d)}
    (hrun : IsKatyushaNsRun fi L D ψ x0 x y z xt) :
    ∀ S : ℕ, 1 ≤ S →
      seqAvg hn (S * (2 * n)) (fun ω =>
          1 / tau1 (S - 1) ^ 2 * (Fobj fi ψ (y ω (S * (2 * n))) - Fobj fi ψ xstar) +
            (tau1 (S - 1) + 1 / 2) / tau1 (S - 1) ^ 2 *
              ∑ j ∈ Finset.Ico 1 (2 * n),
                (Fobj fi ψ (y ω ((S - 1) * (2 * n) + j)) - Fobj fi ψ xstar) +
            3 * L / 2 * ‖z ω (S * (2 * n)) - xstar‖ ^ 2) ≤
        (1 - tau1 0 - 1 / 2) / tau1 0 ^ 2 * (Fobj fi ψ x0 - Fobj fi ψ xstar) +
          (1 / 2) * (2 * n : ℝ) / tau1 0 ^ 2 * (Fobj fi ψ x0 - Fobj fi ψ xstar) +
          3 * L / 2 * ‖x0 - xstar‖ ^ 2 := by sorry

end KatyushaNs
