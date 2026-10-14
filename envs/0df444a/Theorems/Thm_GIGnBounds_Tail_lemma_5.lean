-- Prove2me | Theorems.Thm_GIGnBounds_Tail_lemma_5
-- name    : GIGnBounds.Tail.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:22:05.168356+00:00
-- url     : https://prove2.me/theorems/354da66f-0abb-4910-b94d-48c6689c844f
-- title:
--   Lemma 5 — $E|\sum_{i=1}^nN_{e,i}(t)-nt|^r$ bound for $t\ge1$
-- statement:
--   Let $\mathbb E[S]=1$ and $\mathbb E[S^r]<\infty$ for some $r\ge2$. Let $\{\mathcal N_{e,i},1\le i\le n\}$ be independent equilibrium renewal processes with renewals distributed as $S$, with counts $N_{e,i}(t)$.
--
--   **Lemma 5.** For all $n\ge1$ and $t\ge1$, $\mathbb E\big[|\sum_{i=1}^nN_{e,i}(t)-nt|^r\big]$ is at most
--
--   $$\Big(.76\,(\mathbb E[S^2]+1)^r\,1032^r\,r^{2r}+.21\,(\mathbb E[S^2]+1)\,516^r\,r^{1.5r}\,(\mathbb E[S^r]+1)\Big)(nt)^{\frac r2}.$$
--
--   It verifies hypothesis (i) of Lemma 4 / (ii) of Theorem 10 with $r_1=r$, $s=r/2$.
--
--   **Formalization Note.** The left side is a lower Lebesgue integral, so the conclusion includes its finiteness. $\mathbb E[S^2]$, $\mathbb E[S^r]$ are real integrals, finite under the hypotheses.
-- source:
--   Li and Goldberg, Simple and explicit bounds for multi-server queues with 1/(1−ρ) scaling, arXiv:1706.04628v3, p. 27, Lemma 5

import Mathlib
import Definitions.Def_GIGnBounds_Tail_Setting

open MeasureTheory ProbabilityTheory

namespace GIGnBounds.Tail

/-- **Lemma 5** (Li–Goldberg, arXiv:1706.04628v3, p. 27). If `E[S] = 1` and `E[S^r] < ∞` for some
`r ≥ 2`, then for all `n ≥ 1` and `t ≥ 1` the `r`-th absolute central moment of the pooled equilibrium
renewal process `Σ_{i=1}^n N_{e,i}(t)` is at most the explicit bound below. -/
theorem lemma_5 (μS : Measure ℝ) [IsProbabilityMeasure μS] (hS : IsTimeLaw μS) (hS1 : mean μS = 1)
    (r : ℝ) (hr : 2 ≤ r) (hSr : ∫⁻ x, ENNReal.ofReal (x ^ r) ∂μS < ⊤)
    (n : ℕ) (hn : 1 ≤ n) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ServiceFamily Ω P n μS) (t : ℝ) (ht : 1 ≤ t) :
    ∫⁻ ω, ENNReal.ofReal (|∑ i, (F.Ne i ω t : ℝ) - n * t| ^ r) ∂P ≤ ENNReal.ofReal ((76 / 100 * (∫ x, x ^ 2 ∂μS + 1) ^ r * (1032 : ℝ) ^ r * r ^ (2 * r) +
          21 / 100 * (∫ x, x ^ 2 ∂μS + 1) * (516 : ℝ) ^ r * r ^ ((3 : ℝ) / 2 * r) *
            (∫ x, x ^ r ∂μS + 1)) * ((n : ℝ) * t) ^ (r / 2)) := by sorry

end GIGnBounds.Tail
