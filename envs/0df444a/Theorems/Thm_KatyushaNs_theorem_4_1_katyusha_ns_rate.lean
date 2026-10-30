-- Prove2me | Theorems.Thm_KatyushaNs_theorem_4_1_katyusha_ns_rate
-- name    : KatyushaNs.theorem_4_1_katyusha_ns_rate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:56:25.001146+00:00
-- url     : https://prove2.me/theorems/1fd35554-1cae-46b4-a4f1-62a80249f162
-- title:
--   Theorem 4.1: accelerated $O(1/S^2)$ rate of Katyusha$^{\mathrm{ns}}$ for non-strongly convex $\psi$
-- statement:
--   Let $f_1,\dots,f_n : \mathbb{R}^d \to \mathbb{R}$ ($n \ge 1$) be convex and $L$-smooth with $L > 0$, $f = \frac1n\sum_i f_i$, let $\psi$ be convex with effective domain $D$ (possibly $+\infty$ off $D$, not necessarily strongly convex), $F = f + \psi$, $x_0 \in D$, and let $x^* \in D$ minimize $F$. Run Katyusha$^{\mathrm{ns}}$ (Algorithm 2, Option I, $m = 2n$, $\tau_2 = \frac12$, $\tau_{1,s} = \frac{2}{s+4}$, $\alpha_s = \frac{1}{3\tau_{1,s}L}$) from $x_0$ with independent uniform indices, and write $D_k = F(y_k) - F(x^*)$, $\widetilde D^s = F(\widetilde x^s) - F(x^*)$.
--
--   Write $\mathbb{E}$ for the expectation over the indices of the first $Sm$ iterations. Then:
--
--   1. for every number of epochs $S \ge 0$,
--   $$\mathbb{E}\big[F(\widetilde x^S)\big] - F(x^*) \le \frac{16\,\big(F(x_0) - F(x^*)\big)}{(S+3)^2} + \frac{12\,L\,\|x_0 - x^*\|^2}{m\,(S+3)^2};$$
--   2. for every $\varepsilon > 0$ there is $S$ with $\mathbb{E}\big[F(\widetilde x^S)\big] - F(x^*) \le \varepsilon$ whose number of iterations satisfies
--   $$S\cdot m \le 8\Big(\frac{n\sqrt{F(x_0) - F(x^*)}}{\sqrt\varepsilon} + \frac{\sqrt{nL}\,\|x_0 - x^*\|}{\sqrt\varepsilon}\Big).$$
--
--   This is the paper's rate $O\big((F(x_0)-F(x^*))/S^2 + L\|x_0-x^*\|^2/(mS^2)\big)$ and iteration complexity $O\big(n\sqrt{F(x_0)-F(x^*)}/\sqrt\varepsilon + \sqrt{nL}\|x_0-x^*\|/\sqrt\varepsilon\big)$ with explicit constants: an accelerated rate for a directly accelerated stochastic method, a factor $S$ faster than non-accelerated variance-reduced methods such as SAGA.
--
--   Differences from the source:
--   - generalization: E[F(x̃^S)] − F(x*) ≤ O((F(x₀) − F(x*))/S² + L‖x₀ − x*‖²/(mS²)) → for every S ≥ 0, ≤ 16(F(x₀) − F(x*))/(S+3)² + 12L‖x₀ − x*‖²/(m(S+3)²); reason: the constants of the proof's last display (p. 27) with τ_{1,0} = τ₂ = 1/2 and τ_{1,S−1} = 2/(S+3), the printed τ²_{1,S} read as τ²_{1,S−1} as the preceding sentence states; the explicit bound implies the O-bound
--   - generalization: ε-additive error using at most O(n√(F(x₀) − F(x*))/√ε + √(nL)‖x₀ − x*‖/√ε) iterations → for every ε > 0 some S has S·m ≤ 8(n√(F(x₀) − F(x*))/√ε + √(nL)‖x₀ − x*‖/√ε) and gap ≤ ε; reason: explicit constant 8, obtained from clause 1 with S = max(0, ⌈4a + 3b⌉ − 3), a = √((F(x₀) − F(x*))/ε), b = √(L‖x₀ − x*‖²/(nε)); implies the O-form
--   - reading: "iterations" (with m = Θ(n)) → S·m, the number of inner iterations of Algorithm 2 with m = 2n; reason: the iterations of Algorithm 2 are its inner steps k; Remark 4.2 counts T stochastic iterations as S = T/n epochs up to the constant m/n = 2
--   - generalization: ψ convex and lower semicontinuous (Problem (1.1), p. 1) → ψ convex on its effective domain, no lower semicontinuity; reason: lower semicontinuity only guarantees that the arg mins exist; their existence is part of the hypotheses (the prox predicates / the run). Every lsc convex ψ is covered, so the statement specializes to the paper's
--   - encoding: ψ : ℝᵈ → ℝ ∪ {+∞} → a set D (dom ψ) and real values ψ : ℝᵈ → ℝ with ConvexOn ℝ D ψ (or StrongConvexOn), F = f + ψ on D; reason: every convex extended-valued ψ is of this form and conversely; same instances
--   - encoding: arbitrary starting point x₀ → x₀ ∈ D; reason: for x₀ ∉ dom ψ the paper's right side F(x₀) − F(x*) is +∞ and the claim is vacuous
--   - encoding: x* ∈ arg min_x F(x) → x* ∈ D with F(x*) ≤ F(w) for all w ∈ D; reason: F = +∞ off D, so the minimizers of F are exactly these points
--   - reading: Algorithm 2 with Option I or Option II → Option I only (line 12); reason: the paper states "we analyze only I" (Algorithm 2, line 13)
--   - encoding: n and L implicit (n summands, L-smooth) → 0 < n and 0 < L; reason: n = 0 has no summands and L = 0 makes α_s and 1/(4L) undefined; only undefined cases are excluded
--   - encoding: E[·] over the random indices → seqAvg hn N: the uniform average over all index sequences of the first N iterations; reason: the definition of the expectation for independent uniform indices; the averaged quantities depend only on those indices
--   - encoding: the random iterates of Katyusha^ns(x₀, S, L) run for S epochs → functions x, y, z, x̃ of the whole index sequence ω (ℕ → Fin n) satisfying lines 3, 9, 11, 12 (Option I) and 15 for every epoch s (IsKatyushaNsRun); reason: the arg mins are unique (strongly convex objectives on the convex set D), so the iterates are determined by ω, iterate k depends only on ω 0, …, ω (k − 1), and the first S epochs do not depend on the input S (τ_{1,s}, α_s depend on s only); for the paper's lsc ψ every arg min exists, so such a run exists for every ω
-- source:
--   Allen-Zhu, Katyusha: The First Direct Acceleration of Stochastic Gradient Methods, arXiv:1603.05953v6, Theorem 4.1, p. 15 (proof App. C.1, pp. 26–27)

import Mathlib
import Definitions.Def_KatyushaNs_IsConvexLSmooth
import Definitions.Def_KatyushaNs_Fobj
import Definitions.Def_KatyushaNs_IsKatyushaNsRun
import Definitions.Def_KatyushaNs_seqAvg

namespace KatyushaNs

/-- **Theorem 4.1: accelerated `O(1/S²)` rate of Katyusha^ns for non-strongly convex `ψ`.**
Allen-Zhu, *Katyusha: The First Direct Acceleration of Stochastic Gradient Methods*,
arXiv:1603.05953v6, Theorem 4.1, p. 15 (PDF p. 16): "If each fi(x) is convex, L-smooth in
Problem (1.1) and ψ(·) is not necessarily strongly convex, then Katyusha^ns(x₀, S, L) satisfies
E[F(x̃^S)] − F(x*) ≤ O( (F(x₀) − F(x*))/S² + L‖x₀ − x*‖²/(mS²) ).
In other words, choosing m = Θ(n), Katyusha^ns achieves an ε-additive error (i.e.,
E[F(x̃^S)] − F(x*) ≤ ε) using at most O( n√(F(x₀) − F(x*))/√ε + √(nL)‖x₀ − x*‖/√ε )
iterations." Proof: App. C.1, pp. 26–27 (PDF pp. 27–28).

Setting: `F = f + ψ` with `f = (1/n) Σᵢ fᵢ` (Problem (1.1)); each `fᵢ : ℝᵈ → ℝ` convex and
`L`-smooth, `n ≥ 1`, `L > 0`; `ψ` convex (not necessarily strongly convex), possibly `+∞`,
encoded by its effective domain `D` and its finite values on `D`; `x₀ ∈ D`; `x* ∈ D` minimizes
`F`; `(x, y, z, x̃)` is a run of Algorithm 2 (Option I, `m = 2n`) from `x₀` along every index
sequence. Conclusions, with `E` the expectation over the uniform i.i.d. indices of the first
`S·m` iterations:
(1) for every `S ≥ 0`,
`E[F(x̃^S)] − F(x*) ≤ 16 (F(x₀) − F(x*))/(S+3)² + 12 L‖x₀ − x*‖²/(m (S+3)²)`;
(2) for every `ε > 0` there is `S` such that the number of iterations `S·m` is at most
`8 (n√(F(x₀) − F(x*))/√ε + √(nL)‖x₀ − x*‖/√ε)` and `E[F(x̃^S)] − F(x*) ≤ ε`.

**Formalization Note.** The `O(·)` of the paper is made explicit with the constants of the
proof's last display (p. 27), `τ_{1,0} = τ₂ = 1/2` and `τ_{1,S−1} = 2/(S+3)`; the explicit
bounds imply the printed ones. "Iterations" are the `S·m` inner iterations of Algorithm 2.
`E` is `seqAvg hn (S·m)`; `x̃^S` depends only on the indices of the first `S·m` iterations.
The lower semicontinuity of `ψ` assumed in Problem (1.1) is not needed for the statement: it
guarantees that the arg mins of Algorithm 2 exist, and their existence is part of the hypothesis
`hrun`. -/
theorem theorem_4_1_katyusha_ns_rate {d n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    {fi : Fin n → EuclideanSpace ℝ (Fin d) → ℝ} (hfi : ∀ i, IsConvexLSmooth L (fi i))
    {D : Set (EuclideanSpace ℝ (Fin d))} {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hψ : ConvexOn ℝ D ψ) {x0 : EuclideanSpace ℝ (Fin d)} (hx0 : x0 ∈ D)
    {xstar : EuclideanSpace ℝ (Fin d)} (hxs : xstar ∈ D)
    (hmin : ∀ w ∈ D, Fobj fi ψ xstar ≤ Fobj fi ψ w)
    {x y z xt : (ℕ → Fin n) → ℕ → EuclideanSpace ℝ (Fin d)}
    (hrun : IsKatyushaNsRun fi L D ψ x0 x y z xt) :
    (∀ S : ℕ,
        seqAvg hn (S * (2 * n)) (fun ω => Fobj fi ψ (xt ω S)) - Fobj fi ψ xstar ≤
          16 * (Fobj fi ψ x0 - Fobj fi ψ xstar) / ((S : ℝ) + 3) ^ 2 +
            12 * L * ‖x0 - xstar‖ ^ 2 / ((2 * n : ℝ) * ((S : ℝ) + 3) ^ 2)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ S : ℕ,
        ((S * (2 * n) : ℕ) : ℝ) ≤
            8 * ((n : ℝ) * Real.sqrt (Fobj fi ψ x0 - Fobj fi ψ xstar) / Real.sqrt ε +
              Real.sqrt ((n : ℝ) * L) * ‖x0 - xstar‖ / Real.sqrt ε) ∧
          seqAvg hn (S * (2 * n)) (fun ω => Fobj fi ψ (xt ω S)) - Fobj fi ψ xstar ≤ ε) := by sorry

end KatyushaNs
