-- Prove2me | Theorems.Thm_KatyushaNs_eq_C3_base_case
-- name    : KatyushaNs.eq_C3_base_case
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:54:23.639926+00:00
-- url     : https://prove2.me/theorems/80367b64-11e5-48e9-99bf-558870a59a6b
-- title:
--   Eq. (C.3): base case $s = 0$
-- statement:
--   Let $f_1,\dots,f_n : \mathbb{R}^d \to \mathbb{R}$ ($n \ge 1$) be convex and $L$-smooth with $L > 0$, $f = \frac1n\sum_i f_i$, let $\psi$ be convex with effective domain $D$ (possibly $+\infty$ off $D$, not necessarily strongly convex), $F = f + \psi$, $x_0 \in D$, and let $x^* \in D$ minimize $F$. Run Katyusha$^{\mathrm{ns}}$ (Algorithm 2, Option I, $m = 2n$, $\tau_2 = \frac12$, $\tau_{1,s} = \frac{2}{s+4}$, $\alpha_s = \frac{1}{3\tau_{1,s}L}$) from $x_0$ with independent uniform indices, and write $D_k = F(y_k) - F(x^*)$, $\widetilde D^s = F(\widetilde x^s) - F(x^*)$.
--
--   For the first epoch,
--   $$\begin{aligned}&\mathbb{E}\Big[\frac{1}{\tau_{1,0}^2}D_m + \frac{\tau_{1,0}+\tau_2}{\tau_{1,0}^2}\sum_{j=1}^{m-1}D_j\Big]\\ &\le \frac{1-\tau_{1,0}-\tau_2}{\tau_{1,0}^2}D_0 + \frac{\tau_2 m}{\tau_{1,0}^2}\widetilde D^0 + \frac{3L}{2}\|z_0 - x^*\|^2 - \frac{3L}{2}\mathbb{E}\big[\|z_m - x^*\|^2\big],\end{aligned}$$
--   where $\mathbb{E}$ averages over the $m$ indices of epoch $0$. (Here $\tau_{1,0} = \tau_2 = \frac12$, so the coefficient of $D_0$ is $0$.)
--
--   It is (C.1) at $s = 0$ multiplied by $3L$ and rearranged.
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
-- source:
--   Allen-Zhu, Katyusha: The First Direct Acceleration of Stochastic Gradient Methods, arXiv:1603.05953v6, proof of Theorem 4.1 (App. C.1), eq. (C.3), p. 27

import Mathlib
import Definitions.Def_KatyushaNs_IsConvexLSmooth
import Definitions.Def_KatyushaNs_Fobj
import Definitions.Def_KatyushaNs_tau1
import Definitions.Def_KatyushaNs_IsKatyushaNsRun
import Definitions.Def_KatyushaNs_seqAvg

namespace KatyushaNs

/-- **Eq. (C.3): the base case `s = 0`.**
Allen-Zhu, *Katyusha: The First Direct Acceleration of Stochastic Gradient Methods*,
arXiv:1603.05953v6, proof of Theorem 4.1 (App. C.1), eq. (C.3), p. 27 (PDF p. 28): "For the base
case s = 0, we can also rewrite (C.1) as
E[ 1/τ²_{1,0} D_m + (τ_{1,0} + τ₂)/τ²_{1,0} Σ_{j=1}^{m−1} D_j ]
≤ (1 − τ_{1,0} − τ₂)/τ²_{1,0} D_0 + τ₂m/τ²_{1,0} D̃⁰ + 3L/2 ‖z_0 − x*‖² − 3L/2 E[‖z_m − x*‖²]. (C.3)"
Here `D_k = F(y_k) − F(x*)` and `D̃⁰ = F(x̃⁰) − F(x*)`.

Setting: as in Theorem 4.1 (each `fᵢ` convex and `L`-smooth, `n ≥ 1`, `L > 0`; `ψ` convex on its
effective domain `D`; `x₀ ∈ D`; `x* ∈ D` a minimizer of `F`; a run of Katyusha^ns, Option I,
`m = 2n`, `τ₂ = 1/2`). Conclusion: (C.3), with `E` the average over the `m` indices of epoch 0.

**Formalization Note.** `E` is `seqAvg hn m`, the uniform average over the indices of the first
`m` iterations. `D_0`, `D̃⁰` and `z_0` do not depend on the indices and are written inside the
average. The coefficient `(1 − τ_{1,0} − τ₂)/τ²_{1,0}` is kept as printed (its value is `0`). -/
theorem eq_C3_base_case {d n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    {fi : Fin n → EuclideanSpace ℝ (Fin d) → ℝ} (hfi : ∀ i, IsConvexLSmooth L (fi i))
    {D : Set (EuclideanSpace ℝ (Fin d))} {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hψ : ConvexOn ℝ D ψ) {x0 : EuclideanSpace ℝ (Fin d)} (hx0 : x0 ∈ D)
    {xstar : EuclideanSpace ℝ (Fin d)} (hxs : xstar ∈ D)
    (hmin : ∀ w ∈ D, Fobj fi ψ xstar ≤ Fobj fi ψ w)
    {x y z xt : (ℕ → Fin n) → ℕ → EuclideanSpace ℝ (Fin d)}
    (hrun : IsKatyushaNsRun fi L D ψ x0 x y z xt) :
    seqAvg hn (2 * n) (fun ω =>
        1 / tau1 0 ^ 2 * (Fobj fi ψ (y ω (2 * n)) - Fobj fi ψ xstar) +
          (tau1 0 + 1 / 2) / tau1 0 ^ 2 *
            ∑ j ∈ Finset.Ico 1 (2 * n), (Fobj fi ψ (y ω j) - Fobj fi ψ xstar)) ≤
      seqAvg hn (2 * n) (fun ω =>
        (1 - tau1 0 - 1 / 2) / tau1 0 ^ 2 * (Fobj fi ψ (y ω 0) - Fobj fi ψ xstar) +
          (1 / 2) * (2 * n : ℝ) / tau1 0 ^ 2 * (Fobj fi ψ (xt ω 0) - Fobj fi ψ xstar) +
          3 * L / 2 * ‖z ω 0 - xstar‖ ^ 2 -
          3 * L / 2 * ‖z ω (2 * n) - xstar‖ ^ 2) := by sorry

end KatyushaNs
