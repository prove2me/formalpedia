-- Prove2me | Theorems.Thm_LootBox_TB_eq_22
-- name    : LootBox.TB.eq_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:59.317982+00:00
-- url     : https://prove2.me/theorems/52795240-38af-4816-8f2f-032457a98adc
-- title:
--   Eq. (22), pp. 33–34 — Chebyshev tail P(r_N ≤ (1−ϵ)Np/µ) ≤ σ²/((ϵ²/(1−ϵ))Npµ)
-- statement:
--   Let $F$ be a valuation law (non-negative, finite variance) with mean $\mu > 0$ and variance $\sigma^2$. Let $N \ge 1$, $p > 0$ and $0 < \epsilon < 1$. Let $w_0, w_1, \dots$ be i.i.d. with law $F$ and $r_N = \inf\{ j \ge 1 : Np \le w_0 + \dots + w_{j-1} \}$. Then
--
--   $$\mathbb P\Big( r_N \le (1-\epsilon)\,\frac{Np}{\mu} \Big) \;\le\; \frac{\sigma^2}{\frac{\epsilon^2}{1-\epsilon}\, N p\, \mu}.$$
--
--   The event says that the walk reaches the level $Np$ unusually early, which requires the average of the first $\lfloor (1-\epsilon)Np/\mu \rfloor$ valuations to exceed $\mu/(1-\epsilon)$. The bound is the tail estimate used in the upper bound of Theorem 3.
--
--   **Formalization Note** The event $\{ r_N \le x \}$ with $x = (1-\epsilon)Np/\mu$ real is written as "$r_N$ is a finite integer $j$ with $j \le x$". On the page $(1-\epsilon)Np/\mu$ is treated as an integer index of a sum; the inequality holds as stated for every real $x$.
-- source:
--   Chen, Elmachtoub, Hamilton & Lei, Loot Box Pricing and Design, manuscript submitted August 2019 (Management Science doi:10.1287/mnsc.2020.3748), proof of Theorem 3, Eq. (22), pp. 33–34

import Mathlib
import Definitions.Def_LootBox_TB_Setting

namespace LootBox.TB

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

theorem eq_22 (F : Measure ℝ) [IsProbabilityMeasure F] (hF : ValLaw F) (hμ : 0 < mean F)
    (N : ℕ) [NeZero N] (p : ℝ) (hp : 0 < p) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    walkLaw F {w | ∃ j : ℕ, firstPassage w ((N : ℝ) * p) = j ∧
        (j : ℝ) ≤ (1 - ε) * N * p / mean F} ≤
      ENNReal.ofReal (var F / (ε ^ 2 / (1 - ε) * N * p * mean F)) := by sorry

end LootBox.TB
