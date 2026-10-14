-- Prove2me | Theorems.Thm_GIGnBounds_Tail_lemma_6
-- name    : GIGnBounds.Tail.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:22:13.684863+00:00
-- url     : https://prove2.me/theorems/9e488f31-4fcd-4e6d-b346-575a58b5e50d
-- title:
--   Lemma 6 — $E|\sum_{i=1}^nN_{e,i}(t)-nt|^r\le5.2(35(1+E[S^2]))^rr^{2.5r}(nt)^{r/2}$ for $t\in[2/n,1]$
-- statement:
--   Let $\mathbb E[S]=1$ and $\mathbb E[S^2]<\infty$. Let $\{\mathcal N_{e,i},1\le i\le n\}$ be independent equilibrium renewal processes with renewals distributed as $S$, with counts $N_{e,i}(t)$.
--
--   **Lemma 6.** For all $n\ge1$, $r\ge2$ and $t\in[2/n,1]$,
--
--   $$\mathbb E\Big[\Big|\sum_{i=1}^nN_{e,i}(t)-nt\Big|^r\Big]\le5.2\,\big(35(1+\mathbb E[S^2])\big)^r\,r^{2.5r}\,(nt)^{\frac r2}.\qquad(8)$$
--
--   It verifies the short-time hypothesis (ii) of Lemma 4 / (iii) of Theorem 10.
--
--   **Formalization Note.** The left side is a lower Lebesgue integral, so the conclusion includes its finiteness.
-- source:
--   Li and Goldberg, Simple and explicit bounds for multi-server queues with 1/(1−ρ) scaling, arXiv:1706.04628v3, p. 27, Lemma 6, display (8)

import Mathlib
import Definitions.Def_GIGnBounds_Tail_Setting

open MeasureTheory ProbabilityTheory

namespace GIGnBounds.Tail

/-- **Lemma 6** (Li–Goldberg, arXiv:1706.04628v3, p. 27, display (8)). If `E[S] = 1` and `E[S²] < ∞`, then
for all `n ≥ 1`, `r ≥ 2` and `t ∈ [2/n, 1]`,
`E[|Σ_{i=1}^n N_{e,i}(t) − n t|^r] ≤ 5.2 (35(1 + E[S²]))^r r^{2.5 r} (n t)^{r/2}`. -/
theorem lemma_6 (μS : Measure ℝ) [IsProbabilityMeasure μS] (hS : IsTimeLaw μS) (hS1 : mean μS = 1)
    (hS2 : ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂μS < ⊤)
    (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (hr : 2 ≤ r) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ServiceFamily Ω P n μS) (t : ℝ) (ht₁ : 2 / (n : ℝ) ≤ t) (ht₂ : t ≤ 1) :
    ∫⁻ ω, ENNReal.ofReal (|∑ i, (F.Ne i ω t : ℝ) - n * t| ^ r) ∂P ≤ ENNReal.ofReal (52 / 10 * (35 * (1 + ∫ x, x ^ 2 ∂μS)) ^ r * r ^ ((5 : ℝ) / 2 * r) * ((n : ℝ) * t) ^ (r / 2)) := by sorry

end GIGnBounds.Tail
