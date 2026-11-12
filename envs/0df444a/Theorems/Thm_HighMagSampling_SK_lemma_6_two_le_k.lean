-- Prove2me | Theorems.Thm_HighMagSampling_SK_lemma_6_two_le_k
-- name    : HighMagSampling.SK.lemma_6_two_le_k
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T16:23:42.587087+00:00
-- url     : https://prove2.me/theorems/d149d916-76bd-4e75-8a7e-fb36923651bd
-- title:
--   Lemma 6 for $k \ge 2$ (corrected: as printed the lemma fails at $k = 1$ for $\alpha < 0$)
-- statement:
--   **Source** (Lemma 6, p. 19): for $\pi \in \mathcal{P}(\mathcal{X}^d_k)$ with full support, if $\lambda_2(P_R) \le \alpha/(k - 1)$ for all $R \in \binom{[d]}{k-2}$, for some $\alpha < 1$, then the down-up walk $T^{DU,\pi}$ satisfies a $(1 - \alpha)/k$-Poincaré inequality.
--
--   **Variant:** the same statement under the additional hypothesis $k \ge 2$.
--
--   **Difference:** the variant excludes $k = 1$, where the family of links is empty, the hypothesis is vacuous, and the printed conclusion fails for $\alpha < 0$ ($d = 2$, $\pi$ uniform, $\alpha = -1$).
-- source:
--   Kumar, Sarkar, Tian, Zhu, High-Magnetization Sampling at Low Temperatures, arXiv:2609.08873v1, p. 19, Lemma 6 (corrected: k ≥ 2)

import Mathlib
import Definitions.Def_HighMagSampling_SK_MarkovChain
import Definitions.Def_HighMagSampling_SK_DownUp
import Definitions.Def_HighMagSampling_SK_Spectral

open MeasureTheory ProbabilityTheory

namespace HighMagSampling.SK

theorem lemma_6_two_le_k (d k : ℕ) (hk : 2 ≤ k) (hkd : k ≤ d) (π : Measure (Slice d k))
    [IsProbabilityMeasure π] (hfull : ∀ S : Slice d k, π {S} ≠ 0) (α : ℝ) (hα : α < 1)
    (hlink : ∀ R : Finset (Fin d), R.card + 2 = k →
      ((k : ℝ) - 1) * lambdaTwoRW (linkWeight π R) ≤ α) :
    SatisfiesPoincare (downUp π) π ((1 - α) / k) := by sorry

end HighMagSampling.SK
