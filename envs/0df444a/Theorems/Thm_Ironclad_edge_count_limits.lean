-- Prove2me | Theorems.Thm_Ironclad_edge_count_limits
-- name    : Ironclad.edge_count_limits
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:26:36.250553+00:00
-- url     : https://prove2.me/theorems/2134569b-b736-4139-8a52-2606a7dd11a5
-- title:
--   Appendix .2.3, pp.30–31 — the three edge-count limits in the proof of Lemma 3.1
-- statement:
--   Let $0<p_h<1$, $0<q<1$, $\Delta\ge1$, $\theta\in\mathbb R$ and let $w$ be an i.i.d. honest characteristic string. Write $\#_L(S_i\xrightarrow{\sigma}S_0)$ for the number of transitions out of $S_i$ by pattern $\sigma$ within the first $L$ slots, and $A=\sum_{j=0}^2\pi_j\mu_j$. Then almost surely
--
--   $$
--   \frac{\#_L(S_0\xrightarrow{\sigma_2}S_0)}{L}\to\frac{P_{00}\mathbb P(\sigma_2)}{\mu_{00}[\mathbb P(\sigma_2)+\mathbb P(\sigma_4)]}=\frac{\pi_0P_{00}\mathbb P(\sigma_2)}{A\,[\mathbb P(\sigma_2)+\mathbb P(\sigma_4)]},
--   $$
--   $$
--   \frac{\theta\,\#_L(S_0\xrightarrow{\sigma_4}S_0)}{L}\to\frac{\theta\pi_0P_{00}\mathbb P(\sigma_4)}{A\,[\mathbb P(\sigma_2)+\mathbb P(\sigma_4)]},\qquad \frac{\theta\,\#_L(S_1\xrightarrow{\sigma_4}S_0)}{L}\to\frac{\theta\pi_1P_{10}\mathbb P(\sigma_4)}{A\,[\mathbb P(\sigma_2)+\mathbb P(\sigma_4)]},
--   $$
--
--   as $L\to\infty$, where $1/\mu_{ii}=\pi_i/A$ by the theorem of [29] quoted on p.31.
--
--   These are the three printed terms of $\alpha$; the fourth, $\#_L(S_2\xrightarrow{\sigma_4}S_0\xrightarrow{\sigma_2}S_0)/L$ ("other terms can be computed similarly"), is part of Lemma 3.1.
--
--   Differences from the source:
--   - reading: $\sigma_3=\{H\}\|\{0,h\}^k$, $k\le\Delta$ (Definition 3.1) → $k<\Delta$; reason: the printed $\mathbb P(\sigma_3)$, $\mathbb P(\sigma_4)$ (p.9), on which the matrix (3) and the limits rest, hold only for $k<\Delta$
--   - reading: $1/\mu_{00}$, $1/\mu_{11}$ in the limits → $\pi_0/A$, $\pi_1/A$; reason: the theorem of [29] the paper quotes on p.31; $\mu_{ii}$ has no formula in the paper
--   - generalization: $\theta>1$ (p.5) → any real $\theta$; reason: specializes; the second and third limits are $\theta$ times a limit
--   - reading: no parameter range in App. .2.3 → $0<p_h<1$, $0<q<1$, $\Delta\ge1$; reason: the proper parameters of Theorem 3.2
--   - encoding: the counting window of $\#_L$ (patterns lying in slots $0,\dots,L-1$); decomposition from the first nonzero symbol with $X_0=S_0$; the i.i.d. law as hypotheses on an arbitrary probability space; reason: boundary effects change counts by $O(1)$ and do not affect the limits
-- source:
--   Zhang, Gong, Li, Wu & Zhang, Improving Blockchain Consistency by Assigning Weights to Random Blocks, arXiv:2107.10467v2, Appendix .2.3, proof of Lemma 3.1, p.30 (last display) and p.31 (first display), with p.31 ("The theorem in [29] shows")

import Mathlib
import Definitions.Def_Ironclad_Model
import Definitions.Def_Ironclad_Decomposition
import Definitions.Def_Ironclad_ClosedForms

open MeasureTheory ProbabilityTheory Filter Topology

namespace Ironclad

/-- The three edge-count limits in the proof of Lemma 3.1, Zhang, Gong, Li, Wu & Zhang,
*Improving Blockchain Consistency by Assigning Weights to Random Blocks*, arXiv:2107.10467v2, Appendix .2.3, p.30 (last display) and p.31 (first display): almost surely
1. `#_L(S₀ −σ₂→ S₀)/L → P₀₀P(σ₂)/(μ₀₀[P(σ₂) + P(σ₄)])`,
2. `θ#_L(S₀ −σ₄→ S₀)/L → θP₀₀P(σ₄)/(μ₀₀[P(σ₂) + P(σ₄)])`,
3. `θ#_L(S₁ −σ₄→ S₀)/L → θP₁₀P(σ₄)/(μ₁₁[P(σ₂) + P(σ₄)])`,

with `1/μ_ii = π_i/Σ_j π_j μ_j` (the theorem of [29] quoted on p.31).

**Formalization Note** `#_L(S_i −σ→ S₀)` is `cntTrans … i σ`: transitions out of `S_i` by pattern `σ`
whose pattern lies in the slots `0, …, L − 1`. `θ` is any real number. The i.i.d. honest string is
`IsHonestString μ w ph q` on an arbitrary probability space; slots are indexed from `0`; the
standing parameter range `0 < p_h, q < 1`, `Δ ≥ 1` is that of Theorem 3.2. -/
theorem edge_count_limits {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (w : ℕ → Ω → Sym) (ph q : ℝ) (Δ : ℕ) (hph0 : 0 < ph) (hph1 : ph < 1) (hq0 : 0 < q)
    (hq1 : q < 1) (hΔ : 1 ≤ Δ) (hw : IsHonestString μ w ph q) (θ : ℝ) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun L : ℕ => (cntTrans Δ (fun t => w t ω) L 0 .s2 : ℝ) / L) atTop
          (𝓝 (piStat ph q Δ 0 * Pmat ph q Δ 0 0 * patProb ph q Δ .s2 /
            (meanCycle ph q Δ * (patProb ph q Δ .s2 + patProb ph q Δ .s4)))) ∧
      Tendsto (fun L : ℕ => θ * (cntTrans Δ (fun t => w t ω) L 0 .s4 : ℝ) / L) atTop
          (𝓝 (θ * piStat ph q Δ 0 * Pmat ph q Δ 0 0 * patProb ph q Δ .s4 /
            (meanCycle ph q Δ * (patProb ph q Δ .s2 + patProb ph q Δ .s4)))) ∧
      Tendsto (fun L : ℕ => θ * (cntTrans Δ (fun t => w t ω) L 1 .s4 : ℝ) / L) atTop
          (𝓝 (θ * piStat ph q Δ 1 * Pmat ph q Δ 1 0 * patProb ph q Δ .s4 /
            (meanCycle ph q Δ * (patProb ph q Δ .s2 + patProb ph q Δ .s4)))) := by sorry

end Ironclad
