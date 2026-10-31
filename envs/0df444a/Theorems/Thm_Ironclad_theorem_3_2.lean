-- Prove2me | Theorems.Thm_Ironclad_theorem_3_2
-- name    : Ironclad.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:26:44.662601+00:00
-- url     : https://prove2.me/theorems/b31af1b6-296d-4cfb-85a8-c5fbb8a13bde
-- title:
--   Theorem 3.2 — Ironclad's normalized minimal adversarial mining-power requirement strictly exceeds Nakamoto's ($\mathcal R>1$)
-- statement:
--   Let $0<p_h<1$, $0<q<1$, $\Delta\ge1$ and $\theta\ge1$, and let $w$ be an i.i.d. honest characteristic string: each slot holds an honest regular block with probability $(1-q)p_h$, an honest iron block with probability $qp_h$, and nothing with probability $1-p_h$. Let $\alpha_L$ be the minimal mining-power requirement of the first $L$ slots (Lemma 3.1, p.13), and let $\alpha_0=p_h(1-p_h)^{2\Delta}$ be Nakamoto's requirement, i.e. (4) at $q=0$. Then $\alpha_L$ converges almost surely to a constant $\alpha$, and the relative performance satisfies
--
--   $$
--   \mathcal R=\frac{\alpha/(\theta q+1-q)}{\alpha_0/1}>1.
--   $$
--
--   That is, normalized by the mean block weight $\theta q+1-q$, the mining power an adversary needs to break convergence under Ironclad strictly exceeds what it needs under Nakamoto's protocol, for every delay, every honest block rate and every positive iron-block probability.
--
--   Differences from the source:
--   - generalization: $\theta\ge\max\{\underline\theta,1\}$ with $\underline\theta$ of Equation (7) → $\theta\ge1$; reason: every admissible $\theta$ is $\ge1$, and $\underline\theta$ depends on a constant $\epsilon$ the theorem never fixes; the statement for $\theta\ge1$ specializes to the source's
--   - reading: $\mathcal R$ defined from "the" $\alpha$ of Lemma 3.1 → there exists $\alpha$ with $\alpha_L\to\alpha$ almost surely and $\mathcal R(\alpha)>1$; reason: $\alpha$ is defined as that limit, so its existence is part of the claim
--   - reading: $\sigma_3=\{H\}\|\{0,h\}^k$, $k\le\Delta$ (Definition 3.1) → $k<\Delta$; reason: the printed $\mathbb P(\sigma_3)$, $\mathbb P(\sigma_4)$ (p.9), on which (4) and the proof rest, hold only for $k<\Delta$
--   - encoding: the counting window of $\#_L$ (patterns lying in slots $0,\dots,L-1$); decomposition from the first nonzero symbol with initial state $S_0$; the i.i.d. law as hypotheses on an arbitrary probability space; slots from $0$; reason: the paper fixes none of these; boundary effects change $L\alpha_L$ by $O(1)$ and do not affect the limit
-- source:
--   Zhang, Gong, Li, Wu & Zhang, Improving Blockchain Consistency by Assigning Weights to Random Blocks, arXiv:2107.10467v2, Theorem 3.2, p.14 (R and α₀ defined on p.14; α on p.13; proof in Appendix .2.6, pp.32–33)

import Mathlib
import Definitions.Def_Ironclad_Model
import Definitions.Def_Ironclad_Decomposition
import Definitions.Def_Ironclad_ClosedForms

open MeasureTheory ProbabilityTheory Filter Topology

namespace Ironclad

/-- Theorem 3.2, Zhang, Gong, Li, Wu & Zhang,
*Improving Blockchain Consistency by Assigning Weights to Random Blocks*, arXiv:2107.10467v2, p.14: the relative performance
ratio `R = (α/(θq + 1 − q))/(α₀/1) > 1` for all proper parameters `0 < p_h, q < 1`, `Δ ≥ 1`,
`θ ≥ 1`, where `α = lim_{L→∞} α_L` is the minimal mining power requirement of Lemma 3.1 (an
almost-sure limit, whose existence is part of the conclusion) and `α₀ = p_h(1 − p_h)^{2Δ}` is
Nakamoto's (equation (4) at `q = 0`).

**Formalization Note** The paper requires `θ ≥ max{θ̲, 1}` with `θ̲` of Equation (7); the statement
assumes only `θ ≥ 1`, which covers every admissible `θ`. The honest string is
`IsHonestString μ w ph q` on an arbitrary probability space; slots are indexed from `0`; `α_L`
counts the transitions whose pattern lies in the slots `0, …, L − 1`, from the initial state
`S₀`; the σ₃ boundary is `k < Δ` (see `Ironclad.step`). -/
theorem theorem_3_2 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (w : ℕ → Ω → Sym) (ph q : ℝ) (Δ : ℕ) (hph0 : 0 < ph) (hph1 : ph < 1) (hq0 : 0 < q)
    (hq1 : q < 1) (hΔ : 1 ≤ Δ) (hw : IsHonestString μ w ph q) (θ : ℝ) (hθ : 1 ≤ θ) :
    ∃ α : ℝ, (∀ᵐ ω ∂μ, Tendsto (fun L : ℕ => alphaL Δ θ (fun t => w t ω) L) atTop (𝓝 α)) ∧
      1 < relPerf ph q Δ θ α := by sorry

end Ironclad
