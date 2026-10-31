-- Prove2me | Theorems.Thm_Ironclad_lemma_3_1
-- name    : Ironclad.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:26:23.973766+00:00
-- url     : https://prove2.me/theorems/fa6543b2-a16a-4660-b2a7-54a9e1ce3ea8
-- title:
--   Lemma 3.1 — $\alpha=\lim_{L\to\infty}\alpha_L$ exists almost surely and equals the $(\pi,P,\mu)$ expression and (4)
-- statement:
--   Let $0<p_h<1$, $0<q<1$, $\Delta\ge1$, $\theta\in\mathbb R$ and let $w$ be an i.i.d. honest characteristic string. Let $\alpha_L$ be the minimal mining-power requirement of the first $L$ slots,
--
--   $$
--   \alpha_L=\frac1L\Big[\#_L(S_0\xrightarrow{\sigma_2}S_0)-\#_L(S_2\xrightarrow{\sigma_4}S_0\xrightarrow{\sigma_2}S_0)+\theta\big(\#_L(S_0\xrightarrow{\sigma_4}S_0)+\#_L(S_1\xrightarrow{\sigma_4}S_0)\big)\Big].
--   $$
--
--   Then $\alpha:=\lim_{L\to\infty}\alpha_L$ exists almost surely and
--
--   $$
--   \alpha=\frac{\pi_0P_{00}\mathbb P(\sigma_2)}{[\mathbb P(\sigma_2)+\mathbb P(\sigma_4)]\sum_i\pi_i\mu_i}\Big(1-\frac{\pi_2P_{20}}{\sum_i\pi_iP_{i0}}\Big)+\theta\,\frac{\pi_0P_{00}\mathbb P(\sigma_4)+\pi_1P_{10}\mathbb P(\sigma_4)}{[\mathbb P(\sigma_2)+\mathbb P(\sigma_4)]\sum_i\pi_i\mu_i},
--   $$
--
--   where $\pi$ is the stationary distribution of the embedded chain and $\mu_i$ the expected time spent in $S_i$ before a transition; moreover this value equals the exact expression
--
--   $$
--   \alpha=\frac1{p_h}\Big[(1-q_H)^\Delta\big(q_h^2(1-p_h)^{2\Delta}+q_Hq_h(1-p_h)^\Delta(1-q_H)^\Delta+\theta p_hq_H(1-q_H)^\Delta\big)\Big].\tag{4}
--   $$
--
--   The almost-sure limit $\alpha$ is the long-run rate of agreement weight that an adversary must match to break convergence; Theorem 3.2 compares it with Nakamoto's.
--
--   Differences from the source:
--   - reading: "$\alpha:=\lim_{L\to\infty}\alpha_L$ is well-defined" → $\alpha_L$ converges almost surely to the displayed constant; reason: p.13 says "$\alpha_L$ converges almost surely to a constant $\alpha$"
--   - generalization: $\theta>1$ (p.5) → any real $\theta$; reason: specializes to $\theta>1$
--   - reading: $\sigma_3=\{H\}\|\{0,h\}^k$, $k\le\Delta$ (Definition 3.1) → $k<\Delta$; reason: the printed $\mathbb P(\sigma_3)$, $\mathbb P(\sigma_4)$ (p.9), on which (4) rests, hold only for $k<\Delta$
--   - reading: no parameter range in Lemma 3.1 → $0<p_h<1$, $0<q<1$, $\Delta\ge1$; reason: the proper parameters of Theorem 3.2
--   - encoding: the counting window of $\#_L$ (patterns lying in slots $0,\dots,L-1$); decomposition from the first nonzero symbol with $X_0=S_0$; the i.i.d. law as hypotheses on an arbitrary probability space; slots from $0$; reason: the paper fixes none of these; boundary effects change $L\alpha_L$ by $O(1)$; the window reproduces the paper's $\alpha_7=\theta/7$ for Figure 4
-- source:
--   Zhang, Gong, Li, Wu & Zhang, Improving Blockchain Consistency by Assigning Weights to Random Blocks, arXiv:2107.10467v2, Lemma 3.1, p.13 (α_L defined on p.13; proof in Appendix .2.3, pp.30–31)

import Mathlib
import Definitions.Def_Ironclad_Model
import Definitions.Def_Ironclad_Decomposition
import Definitions.Def_Ironclad_ClosedForms

open MeasureTheory ProbabilityTheory Filter Topology

namespace Ironclad

/-- Lemma 3.1, Zhang, Gong, Li, Wu & Zhang,
*Improving Blockchain Consistency by Assigning Weights to Random Blocks*, arXiv:2107.10467v2, p.13: the minimal mining power
requirement `α := lim_{L→∞} α_L` is well-defined, it equals the expression in terms of `π`, `P`
and `μ`, and it equals the exact expression (4). Almost surely `α_L` converges to
`alphaPiMu ph q Δ θ`, and `alphaPiMu ph q Δ θ = alphaClosed ph q Δ θ`.

**Formalization Note** "Well-defined" is read as almost-sure convergence of `α_L` (p.13: "`α_L`
converges almost surely to a constant `α`"). `θ` is any real number; the paper has `θ > 1`.
The i.i.d. honest string is
`IsHonestString μ w ph q` on an arbitrary probability space; slots are indexed from `0`; the
standing parameter range `0 < p_h, q < 1`, `Δ ≥ 1` is that of Theorem 3.2. -/
theorem lemma_3_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (w : ℕ → Ω → Sym) (ph q : ℝ) (Δ : ℕ) (hph0 : 0 < ph) (hph1 : ph < 1) (hq0 : 0 < q)
    (hq1 : q < 1) (hΔ : 1 ≤ Δ) (hw : IsHonestString μ w ph q) (θ : ℝ) :
    (∀ᵐ ω ∂μ, Tendsto (fun L : ℕ => alphaL Δ θ (fun t => w t ω) L) atTop
      (𝓝 (alphaPiMu ph q Δ θ))) ∧
    alphaPiMu ph q Δ θ = alphaClosed ph q Δ θ := by sorry

end Ironclad
