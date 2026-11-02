-- Prove2me | Theorems.Thm_NoSignalPA_bernstein_chain
-- name    : NoSignalPA.bernstein_chain
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T16:02:43.443727+00:00
-- url     : https://prove2.me/theorems/d7eb4570-db24-4680-831d-1243768e9788
-- title:
--   Bernstein's construction, the chain ending in (14) (corrected: sign in the last line)
-- statement:
--   Fix a key value $\mathbf k$, real weights $(\mu_{\mathbf a})_{\mathbf a\in\{0,1\}^{N_r}}$, a threshold $J\in\mathbb R$ and $\beta\ge0$. Let $h$ be a uniformly random function $\{0,1\}^{N_r}\to\{0,1\}^{N_s}$, $V_{\mathbf a}=[h(\mathbf a)=\mathbf k]$ and $p=2^{-N_s}$. Then
--
--   $$
--   \begin{aligned}
--   \Pr\Bigl\{\sum_{\mathbf a}\mu_{\mathbf a}V_{\mathbf a}\ge J\Bigr\}
--   &\le \Pr\Bigl\{e^{-\beta J+\beta\sum_{\mathbf a}\mu_{\mathbf a}V_{\mathbf a}}\ge1\Bigr\}
--   \le e^{-\beta J}\bigl\langle e^{\beta\sum_{\mathbf a}\mu_{\mathbf a}V_{\mathbf a}}\bigr\rangle\\
--   &\le e^{-\beta J}\prod_{\mathbf a}\bigl[p\,e^{\beta\mu_{\mathbf a}}+(1-p)\bigr]
--   \le e^{-\beta J}\prod_{\mathbf a}\bigl[1+p\,(\beta\mu_{\mathbf a}+\beta^2\mu_{\mathbf a}^2)\bigr]\\
--   &\le \exp\Bigl[-\beta J+p\sum_{\mathbf a}(\beta\mu_{\mathbf a}+\beta^2\mu_{\mathbf a}^2)\Bigr],
--   \end{aligned}
--   $$
--
--   where $\langle\cdot\rangle$ is the average over $h$, and the fourth inequality, (14), is asserted under the constraint $|\beta\mu_{\mathbf a}|\le1$ for all $\mathbf a$ (the paper's "in (14) we need"); the other four hold for every $J$ and $\beta\ge0$. Each of the five inequalities is part of the statement. This exponential-moment bound is the probabilistic core of Lemma 2.
--
--   Differences from the source:
--   - generalization: weights μ_a = Γ_a(a₀, b₀, x₀, y₀) with the constraint |β 5^M 8^{−Nr}| ≤ 1 → arbitrary real weights μ_a, with |β μ_a| ≤ 1 for all a as the hypothesis of the fourth inequality (14) only; reason: by |μ_a| ≤ 5^M 8^{−Nr} (milestone abs_mu_le) the printed constraint implies |β μ_a| ≤ 1, so the statement specializes to the paper's
--   - correction: last line exp[− βJ 2^{−Ns} Σ_a(βµ_a + β²µ_a²)] → exp[−βJ + 2^{−Ns} Σ_a(βµ_a + β²µ_a²)]; reason: as printed (a product) the last inequality is false: for J = 0, β = 1, all μ_a = 1/2, the left side ∏_a[1 + 2^{−Ns}·3/4] exceeds 1 = exp(0); the + sign, forced by 1 + t ≤ e^t applied to the previous line, was lost
--   - encoding: ⟨e^{β Σ_a µ_a V_a}⟩ and Prob over a random h → uniformExp and OAI.ThorpCompatibility.uniformProbability over all functions h, V_a = 1 if h(a) = k else 0; reason: the paper's expectation and probability are over a uniformly random h (p.5)
-- source:
--   Masanes, Universally-composable privacy amplification from causality constraints, arXiv:0807.2158v4, Appendix, proof of Lemma 2, eq. (14), p.5

import Mathlib
import Definitions.Def_NoSignalPA_Str
import Definitions.Def_OAI_Probability_ThorpCompatibility_PermutationProbability
import Definitions.Def_NoSignalPA_uniformExp

namespace NoSignalPA

/-- **Bernstein's construction, the chain ending in (14).**
Ll. Masanes, *Universally-composable privacy amplification from causality constraints*,
arXiv:0807.2158v4, Appendix, proof of Lemma 2, eq. (14), p. 5 (PDF p. 5): "Following Bernstein's contruction,
for any J and β ≥ 0 we have `Prob{Σ_a µ_a V_a ≥ J} ≤ Prob{e^{−βJ+β Σ_a µ_a V_a} ≥ 1}
≤ e^{−βJ} ⟨e^{β Σ_a µ_a V_a}⟩ ≤ e^{−βJ} Π_a [2^{−Ns} e^{βµ_a} + (1 − 2^{−Ns})]
≤ e^{−βJ} Π_a [1 + 2^{−Ns} (βµ_a + β²µ_a²)] (14) ≤ exp[− βJ 2^{−Ns}Σ_a(βµ_a + β²µ_a²)]`
where in (14) we need `|β 5^M 8^{−Nr}| ≤ 1`."

Fix a key `k`, real weights `μ_a` (`a ∈ {0,1}^{Nr}`), a threshold `J` and `β ≥ 0`. With
`V_a = [h(a) = k]` for a uniformly random `h` and `p = 2^{−Ns}`, each of the five inequalities of
the chain holds; the fourth, (14), under the constraint `|β μ_a| ≤ 1` for all `a`, as on the page.

**Formalization Note.** (1) Generalization: the weights are arbitrary reals, and the constraint
of (14) is `|βμ_a| ≤ 1`, attached to (14) only; for `μ_a = Γ_a(a₀, b₀, x₀, y₀)` it follows from
the printed constraint `|β 5^M 8^{−Nr}| ≤ 1` and `|μ_a| ≤ 5^M 8^{−Nr}` (milestone `abs_mu_le`). (2) Encoding: the last line is
`exp[−βJ + 2^{−Ns} Σ_a (βμ_a + β²μ_a²)]`; the printed line has lost the `+`, which the previous
line forces. (3) `⟨·⟩` is the average over `h` (`uniformExp`). -/
theorem bernstein_chain {Nr Ns : ℕ} (k : Str Ns) (μ : Str Nr → ℝ) (J β : ℝ) (hβ : 0 ≤ β) :
    let V : (Str Nr → Str Ns) → Str Nr → ℝ := fun h a => if h a = k then 1 else 0
    let p : ℝ := ((2 : ℝ) ^ Ns)⁻¹
    OAI.ThorpCompatibility.uniformProbability (fun h => J ≤ ∑ a, μ a * V h a)
        ≤ OAI.ThorpCompatibility.uniformProbability (fun h => 1 ≤ Real.exp (-β * J + β * ∑ a, μ a * V h a)) ∧
      OAI.ThorpCompatibility.uniformProbability (fun h => 1 ≤ Real.exp (-β * J + β * ∑ a, μ a * V h a))
        ≤ Real.exp (-β * J) * uniformExp (fun h => Real.exp (β * ∑ a, μ a * V h a)) ∧
      Real.exp (-β * J) * uniformExp (fun h => Real.exp (β * ∑ a, μ a * V h a))
        ≤ Real.exp (-β * J) * ∏ a, (p * Real.exp (β * μ a) + (1 - p)) ∧
      ((∀ a, |β * μ a| ≤ 1) →
        Real.exp (-β * J) * ∏ a, (p * Real.exp (β * μ a) + (1 - p))
          ≤ Real.exp (-β * J) * ∏ a, (1 + p * (β * μ a + β ^ 2 * μ a ^ 2))) ∧
      Real.exp (-β * J) * ∏ a, (1 + p * (β * μ a + β ^ 2 * μ a ^ 2))
        ≤ Real.exp (-β * J + p * ∑ a, (β * μ a + β ^ 2 * μ a ^ 2)) := by sorry

end NoSignalPA
