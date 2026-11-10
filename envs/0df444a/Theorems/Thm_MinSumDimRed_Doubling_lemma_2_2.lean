-- Prove2me | Theorems.Thm_MinSumDimRed_Doubling_lemma_2_2
-- name    : MinSumDimRed.Doubling.lemma_2_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:34:40.514688+00:00
-- url     : https://prove2.me/theorems/ce883f5f-8891-484c-b777-636d91d36888
-- title:
--   Lemma 2.2 — packing property: an $r$-packing $N$ of a doubling metric space $P$ has $|N| \le (\mathrm{diam}(P)/r)^{O(\mathrm{ddim}(P))}$ (false as printed when $r > \mathrm{diam}(P)$, insight I1)
-- statement:
--   **Lemma 2.2** (Packing Property [GKL03, Proposition 1.1], p. 9), stated as printed. There is an absolute constant $C > 0$ such that for every metric space $P$ that is doubling (so $\mathrm{ddim}(P)$, the least $D \ge 1$ with every ball covered by $2^D$ balls of half the radius, is defined) and every $r$-packing $N \subseteq P$ ($r > 0$, distinct points of $N$ at distance $> r$),
--   $$|N| \le \Big(\frac{\mathrm{diam}(P)}{r}\Big)^{C \cdot \mathrm{ddim}(P)}.$$
--   Cardinality, diameter, quotient and power are taken in $[0, \infty]$, so an infinite $N$ or an unbounded $P$ is covered.
--
--   **Formalization Note** As printed the bound fails whenever $r > \mathrm{diam}(P)$ and $N \ne \emptyset$ (e.g. a one-point space: $1 \le 0$); this is recorded as insight I1, with a machine-checked refutation of this exact statement in `Solutions/verification/MinSumDimRed_Doubling_Checks.lean`. The statement is posed as printed; a solver may disprove it.
--
--   Differences from the source:
--   - reading: exponent O(ddim(P)) → exponent C · ddim(P) with one absolute C > 0 quantified before P, N, r; reason: one absolute exponent multiplier; in the application on p. 13, a radius-r_i ball is packed at scale ε r_i/100, so a standard ball-packing bound gives ε^{-O(ddim)} without the false unrestricted diameter formula
--   - encoding: ddim(P) of a metric space P → ddim Set.univ (infimum of admissible exponents) under the hypothesis ∃ D, IsDoublingWith Set.univ D; reason: nondegeneracy: excludes only spaces whose doubling dimension is undefined (infinite), where the printed exponent is meaningless; on doubling spaces the infimum is attained and is the paper's ddim
--   - encoding: |N| and diam(P) → N.encard (in ℕ∞, cast to ℝ≥0∞) and Metric.ediam Set.univ in ℝ≥0∞, quotient by ENNReal.ofReal r and rpow in ℝ≥0∞; reason: avoids the junk value Metric.diam = 0 on unbounded spaces; for an unbounded P the right side is ∞ and for a bounded P it is the real bound
--   - encoding: a metric space P and N ⊆ P → a type P with [MetricSpace P] and N : Set P; balls and packings relative to Set.univ; reason: same objects
-- source:
--   Asaf Dallal, Robert Krauthgamer, Dimension Reduction and Coresets for Min-Sum k-Clustering, arXiv:2610.38920 (version of November 2, 2026, SHA-256 13a9281e…), p. 9 (PDF 9), Lemma 2.2

import Mathlib
import Definitions.Def_MinSumDimRed_Doubling_Metric

open scoped ENNReal

namespace MinSumDimRed.Doubling

/-- Lemma 2.2 (Packing Property [GKL03, Proposition 1.1]), p. 9, as printed: there is an absolute
constant `C > 0` (the `O(·)`) such that for every doubling metric space `P` and every `r`-packing
`N ⊆ P`, `|N| ≤ (diam(P)/r)^{C · ddim(P)}`. Cardinality and diameter are extended
(`encard`, `Metric.ediam`), so infinite `N` and unbounded `P` are included. -/
theorem lemma_2_2 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Type*) [MetricSpace P],
        (∃ D : ℝ, IsDoublingWith (Set.univ : Set P) D) →
        ∀ (N : Set P) (r : ℝ), IsPacking (Set.univ : Set P) N r →
          ((N.encard : ℕ∞) : ℝ≥0∞) ≤
            (Metric.ediam (Set.univ : Set P) / ENNReal.ofReal r) ^
              (C * ddim (Set.univ : Set P)) := by sorry

end MinSumDimRed.Doubling
