-- Prove2me | Theorems.Thm_KatyushaNs_eq_C2_epoch_recursion
-- name    : KatyushaNs.eq_C2_epoch_recursion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:53:45.589046+00:00
-- url     : https://prove2.me/theorems/0fcb0e3c-ba7a-45b4-af4a-adc66d0a1940
-- title:
--   Eq. (C.2): epoch recursion for $s \ge 1$
-- statement:
--   Let $f_1,\dots,f_n : \mathbb{R}^d \to \mathbb{R}$ ($n \ge 1$) be convex and $L$-smooth with $L > 0$, $f = \frac1n\sum_i f_i$, let $\psi$ be convex with effective domain $D$ (possibly $+\infty$ off $D$, not necessarily strongly convex), $F = f + \psi$, $x_0 \in D$, and let $x^* \in D$ minimize $F$. Run Katyusha$^{\mathrm{ns}}$ (Algorithm 2, Option I, $m = 2n$, $\tau_2 = \frac12$, $\tau_{1,s} = \frac{2}{s+4}$, $\alpha_s = \frac{1}{3\tau_{1,s}L}$) from $x_0$ with independent uniform indices, and write $D_k = F(y_k) - F(x^*)$, $\widetilde D^s = F(\widetilde x^s) - F(x^*)$.
--
--   For every epoch $s \ge 1$, conditionally on the indices of the first $s$ epochs,
--   $$\begin{aligned}&\mathbb{E}\Big[\frac{1}{\tau_{1,s}^2}D_{(s+1)m} + \frac{\tau_{1,s}+\tau_2}{\tau_{1,s}^2}\sum_{j=1}^{m-1}D_{sm+j}\Big]\\ &\le \frac{1-\tau_{1,s}}{\tau_{1,s}^2}D_{sm} + \frac{\tau_2}{\tau_{1,s}^2}\sum_{j=1}^{m-1}D_{(s-1)m+j} + \frac{3L}{2}\|z_{sm} - x^*\|^2 - \frac{3L}{2}\mathbb{E}\big[\|z_{(s+1)m} - x^*\|^2\big],\end{aligned}$$
--   where $\mathbb{E}$ averages over the $m$ indices of epoch $s$.
--
--   It follows from (C.1) with $\alpha_s = 1/(3\tau_{1,s}L)$ and the convexity bound $m\widetilde D^s \le \sum_{j=1}^m D_{(s-1)m+j}$, and is the recursion that is telescoped over the epochs.
--
--   Differences from the source:
--   - generalization: ψ convex and lower semicontinuous (Problem (1.1), p. 1) → ψ convex on its effective domain, no lower semicontinuity; reason: lower semicontinuity only guarantees that the arg mins exist; their existence is part of the hypotheses (the prox predicates / the run). Every lsc convex ψ is covered, so the statement specializes to the paper's
--   - encoding: ψ : ℝᵈ → ℝ ∪ {+∞} → a set D (dom ψ) and real values ψ : ℝᵈ → ℝ with ConvexOn ℝ D ψ (or StrongConvexOn), F = f + ψ on D; reason: every convex extended-valued ψ is of this form and conversely; same instances
--   - encoding: arbitrary starting point x₀ → x₀ ∈ D; reason: for x₀ ∉ dom ψ the paper's right side F(x₀) − F(x*) is +∞ and the claim is vacuous
--   - encoding: x* ∈ arg min_x F(x) → x* ∈ D with F(x*) ≤ F(w) for all w ∈ D; reason: F = +∞ off D, so the minimizers of F are exactly these points
--   - reading: Algorithm 2 with Option I or Option II → Option I only (line 12); reason: the paper states "we analyze only I" (Algorithm 2, line 13)
--   - encoding: n and L implicit (n summands, L-smooth) → 0 < n and 0 < L; reason: n = 0 has no summands and L = 0 makes α_s and 1/(4L) undefined; only undefined cases are excluded
--   - encoding: E[·] with the randomness of the first s − 1 epochs fixed → condAvg hn p m: the first s·m indices fixed to a prefix p, the m indices of epoch s averaged uniformly; terms that depend only on p are written inside the average; reason: the definition of the conditional expectation for independent uniform indices; a constant inside a uniform average keeps its value
--   - encoding: the random iterates of Katyusha^ns(x₀, S, L) run for S epochs → functions x, y, z, x̃ of the whole index sequence ω (ℕ → Fin n) satisfying lines 3, 9, 11, 12 (Option I) and 15 for every epoch s (IsKatyushaNsRun); reason: the arg mins are unique (strongly convex objectives on the convex set D), so the iterates are determined by ω, iterate k depends only on ω 0, …, ω (k − 1), and the first S epochs do not depend on the input S (τ_{1,s}, α_s depend on s only); for the paper's lsc ψ every arg min exists, so such a run exists for every ω
-- source:
--   Allen-Zhu, Katyusha: The First Direct Acceleration of Stochastic Gradient Methods, arXiv:1603.05953v6, proof of Theorem 4.1 (App. C.1), eq. (C.2), p. 27

import Mathlib
import Definitions.Def_KatyushaNs_IsConvexLSmooth
import Definitions.Def_KatyushaNs_Fobj
import Definitions.Def_KatyushaNs_tau1
import Definitions.Def_KatyushaNs_IsKatyushaNsRun
import Definitions.Def_KatyushaNs_condAvg

namespace KatyushaNs

/-- **Eq. (C.2): the epoch recursion for `s ≥ 1`.**
Allen-Zhu, *Katyusha: The First Direct Acceleration of Stochastic Gradient Methods*,
arXiv:1603.05953v6, proof of Theorem 4.1 (App. C.1), eq. (C.2), p. 27 (PDF p. 28): "If we define
x̃^s = (1/m) Σ_{j=1}^m y_{(s−1)m+j}, then by the convexity of function F(·) we have
m D̃^s ≤ Σ_{j=1}^n D_{(s−1)m+j}. Therefore, using the parameter choice α_s = 1/(3τ_{1,s}L), for
every s ≥ 1 we can derive from (C.1) that
E[ 1/τ²_{1,s} D_{(s+1)m} + (τ_{1,s} + τ₂)/τ²_{1,s} Σ_{j=1}^{m−1} D_{sm+j} ]
≤ (1 − τ_{1,s})/τ²_{1,s} D_{sm} + τ₂/τ²_{1,s} Σ_{j=1}^{m−1} D_{(s−1)m+j} + 3L/2 ‖z_{sm} − x*‖²
− 3L/2 E[‖z_{(s+1)m} − x*‖²]. (C.2)"
Here `D_k = F(y_k) − F(x*)`.

Setting: as in Theorem 4.1 (each `fᵢ` convex and `L`-smooth, `n ≥ 1`, `L > 0`; `ψ` convex on its
effective domain `D`; `x₀ ∈ D`; `x* ∈ D` a minimizer of `F`; a run of Katyusha^ns, Option I,
`m = 2n`, `τ₂ = 1/2`). Conclusion: for every epoch `s ≥ 1` and every choice `p` of the indices of
the first `s·m` iterations, (C.2) holds with `E` the average over the indices of epoch `s`.

**Formalization Note.** The conditional expectation given the earlier epochs is `condAvg hn p m`
(see (C.1)). The terms on the right other than the last depend only on `p` and are written inside
the average, which leaves their value unchanged. The sums `Σ_{j=1}^{m−1}` are over
`Finset.Ico 1 (2n)`. In the quoted convexity sentence the printed upper limit `n` of
`Σ_{j=1}^n D_{(s−1)m+j}` is read as `m` (the definition of `x̃^s` just before it averages `m`
terms); it does not enter the statement. -/
theorem eq_C2_epoch_recursion {d n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    {fi : Fin n → EuclideanSpace ℝ (Fin d) → ℝ} (hfi : ∀ i, IsConvexLSmooth L (fi i))
    {D : Set (EuclideanSpace ℝ (Fin d))} {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hψ : ConvexOn ℝ D ψ) {x0 : EuclideanSpace ℝ (Fin d)} (hx0 : x0 ∈ D)
    {xstar : EuclideanSpace ℝ (Fin d)} (hxs : xstar ∈ D)
    (hmin : ∀ w ∈ D, Fobj fi ψ xstar ≤ Fobj fi ψ w)
    {x y z xt : (ℕ → Fin n) → ℕ → EuclideanSpace ℝ (Fin d)}
    (hrun : IsKatyushaNsRun fi L D ψ x0 x y z xt) :
    ∀ s : ℕ, 1 ≤ s → ∀ p : Fin (s * (2 * n)) → Fin n,
      condAvg hn p (2 * n) (fun ω =>
          1 / tau1 s ^ 2 * (Fobj fi ψ (y ω ((s + 1) * (2 * n))) - Fobj fi ψ xstar) +
            (tau1 s + 1 / 2) / tau1 s ^ 2 *
              ∑ j ∈ Finset.Ico 1 (2 * n), (Fobj fi ψ (y ω (s * (2 * n) + j)) - Fobj fi ψ xstar)) ≤
        condAvg hn p (2 * n) (fun ω =>
          (1 - tau1 s) / tau1 s ^ 2 * (Fobj fi ψ (y ω (s * (2 * n))) - Fobj fi ψ xstar) +
            (1 / 2) / tau1 s ^ 2 *
              ∑ j ∈ Finset.Ico 1 (2 * n),
                (Fobj fi ψ (y ω ((s - 1) * (2 * n) + j)) - Fobj fi ψ xstar) +
            3 * L / 2 * ‖z ω (s * (2 * n)) - xstar‖ ^ 2 -
            3 * L / 2 * ‖z ω ((s + 1) * (2 * n)) - xstar‖ ^ 2) := by sorry

end KatyushaNs
