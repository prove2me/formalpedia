-- Prove2me | Theorems.Thm_KingmanSubadditive_StationaryIncrements_series_divergent
-- name    : KingmanSubadditive.StationaryIncrements.series_divergent
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:43:05.369927+00:00
-- url     : https://prove2.me/theorems/875ea272-dc45-4216-bc4f-1eaa20ec278e
-- title:
--   Proof of Theorem 3, p. 889 — $\sum_n P\{\nu_n>\Gamma(n+\frac12)\}\ge\sum_n\sum_{r\ge n}\frac1{r(r+1)}=\infty$
-- statement:
--   In the construction of the proof of Theorem 3 ($\Gamma$ positive and non-decreasing on $(0,\infty)$, and $\nu_0,\nu_1,\dots$ random variables, each with law $m_\Gamma$, together with an independent uniform $\eta$),
--   $$ \sum_{n=1}^\infty P\{\nu_n>\Gamma(n+\tfrac12)\}\;\ge\;\sum_{n=1}^\infty\sum_{r=n}^\infty\frac{1}{r(r+1)}\;=\;\infty . $$
--
--   Combined with the independence of the $\nu_n$, this divergence is the hypothesis of the second Borel–Cantelli lemma in the proof of Theorem 3.
--
--   **Formalization Note** All sums are in $[0,\infty]$ (`ℝ≥0∞`), where they always exist. The ranges $n\ge1$ and $r\ge n$ are subtypes of $\mathbb N$.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, p. 889, §1.4, proof of Theorem 3

import Mathlib
import Definitions.Def_KingmanSubadditive_StationaryIncrements_Stationarity
import Definitions.Def_KingmanSubadditive_StationaryIncrements_Construction
open MeasureTheory ProbabilityTheory Filter

namespace KingmanSubadditive.StationaryIncrements

/-- **Proof of Theorem 3, p. 889 (unnumbered; §1.4)** — Kingman, *Subadditive ergodic theory*, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798.

"`Σ_{n=1}^∞ P{ν_n > Γ(n + ½)} ≥ Σ_{n=1}^∞ Σ_{r=n}^∞ 1/(r(r + 1)) = ∞`."

For the construction of the proof of Theorem 3 (`Γ` positive and increasing on `(0, ∞)`,
`IsConstruction Γ P η ν`),
$$ \sum_{n\ge1} P\{\nu_n > \Gamma(n+\tfrac12)\} \;\ge\; \sum_{n\ge1}\sum_{r\ge n}\frac{1}{r(r+1)} = \infty . $$

**Formalization Note.** All sums are `tsum`s in `ℝ≥0∞`, where they always exist; the index sets
`n ≥ 1` and `r ≥ n` are subtypes of `ℕ`. -/
theorem series_divergent {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Γ : ℝ → ℝ) (hΓpos : ∀ t : ℝ, 0 < t → 0 < Γ t)
    (hΓmono : MonotoneOn Γ (Set.Ioi 0)) (η : Ω → ℝ) (ν : ℕ → Ω → ℕ)
    (hC : IsConstruction Γ P η ν) :
    (∑' n : {n : ℕ // 1 ≤ n}, ∑' r : {r : ℕ // (n : ℕ) ≤ r},
        ENNReal.ofReal (1 / ((r : ℝ) * ((r : ℝ) + 1))))
        ≤ ∑' n : {n : ℕ // 1 ≤ n}, P {ω | Γ ((n : ℝ) + 1 / 2) < (ν n ω : ℝ)} ∧
      (∑' n : {n : ℕ // 1 ≤ n}, ∑' r : {r : ℕ // (n : ℕ) ≤ r},
        ENNReal.ofReal (1 / ((r : ℝ) * ((r : ℝ) + 1)))) = ⊤ := by sorry

end KingmanSubadditive.StationaryIncrements
