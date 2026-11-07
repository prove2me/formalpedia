-- Prove2me | Theorems.Thm_GaussPart_lemma_3_9
-- name    : GaussPart.lemma_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:31:52.429257+00:00
-- url     : https://prove2.me/theorems/b5659cb9-d099-4df9-b5bf-abc13b59868b
-- title:
--   Lemma 3.9 — negligible mass of the Gaussian tail cells
-- statement:
--   Let $P=N(0,I_d)$, let $Q$ be $(q,\sigma)$-smooth with respect to $P$ ($q\ge1$, $\sigma\in(0,1]$), $L\ge1$, $\eta\in(0,1)$, and let $T>0$ satisfy $T^2\ge2\log\big(200L/(\sigma\eta/100)^q\big)$. Consider Algorithm 1 through iteration $L$, and let $\mathcal T_t$ be the tail cells of $\mathcal U_t$. Then for every $t\le L+1$
--   $$\sum_{R\in\mathcal T_t}Q(R)\le\frac{(2Le^{-T^2/2})^{1/q}}{\sigma}\le\frac{\eta}{100}.$$
--
--   Tail children are unbounded along their split direction and are discarded; the lemma shows they carry negligible mass.
--
--   **Formalization Note** Algorithm 1 is a valid trace with knobs $K$ ($K.L=L$, $K.T=T$). No probabilistic event is needed.
--
--   Differences from the source:
--   - generalization: Algorithm 1 through iteration L → any valid trace (GaussPart.Trace): any threshold whose empirical gap is at least 2g instead of a maximizing one, and any refinement (sorted breakpoints, gaps ≤ δ₀, ends beyond ±T, at most m pieces) instead of the exact grid of Definition 3.4; reason: the analysis uses only these properties; Algorithm 1 with Definition 3.4's grid is one valid trace
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Lemma 3.9, p.23 (PDF p.25); Algorithm 1, p.19

import Mathlib
import Definitions.Def_GaussPart_IsSmooth
import Definitions.Def_GaussPart_Trace
import Definitions.Def_GaussPart_TraceEvents

open MeasureTheory ProbabilityTheory

namespace GaussPart

/-- **Lemma 3.9** (Negligible Mass of Gaussian Tail Cells).

arXiv:2611.05264 (copy with sha256 7e0ca6d4…), Lemma 3.9, p.23 (PDF p.25); Algorithm 1, p.19.

"Let P = N(0, I_d), let Q be (q, σ)-smooth with respect to P, where q ≥ 1 and σ ∈ (0, 1], and let
L ∈ ℕ₊ and η ∈ (0, 1). Choose T > 0 satisfying T² ≥ 2 log(200L/(ση/100)^q). Consider Algorithm 1
through iteration L. Then, for every t ≤ L + 1, ∑_{R∈T_t} q_R ≤ (2L e^{−T²/2})^{1/q}/σ ≤ η/100."

**Formalization Note.** "Algorithm 1 through iteration L" is a valid `Trace` with parameters `K`
(`K.L = L`, `K.T = T > 0`). `T_t` is the list of cells of `U_t` tagged as tails (`tr.tagged t
Tag.tail`); a trace's tail children lie beyond `−T` and `T` (Definition 3.4's grid is one such
refinement). The power `1/q` is `Real.rpow`. No probabilistic event is needed. -/
theorem lemma_3_9 {d : ℕ} (Q : Measure (Vec d)) [IsProbabilityMeasure Q] (q σ : ℝ) (hq : 1 ≤ q)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hs : IsSmooth (stdGaussian (Vec d)) Q q σ) (η : ℝ) (hη : 0 < η)
    (hη1 : η < 1) (K : Knobs)
    (hT : 2 * Real.log (200 * (K.L : ℝ) / (σ * η / 100) ^ q) ≤ K.T ^ 2)
    (tr : Trace d) (htr : tr.IsValid K) :
    ∀ t : ℕ, t ≤ K.L + 1 →
      mass Q (tr.tagged t Tag.tail) ≤
          (2 * (K.L : ℝ) * Real.exp (-(K.T ^ 2 / 2))) ^ (1 / q) / σ ∧
        (2 * (K.L : ℝ) * Real.exp (-(K.T ^ 2 / 2))) ^ (1 / q) / σ ≤ η / 100 := by sorry

end GaussPart
