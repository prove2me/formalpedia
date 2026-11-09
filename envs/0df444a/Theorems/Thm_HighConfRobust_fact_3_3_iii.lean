-- Prove2me | Theorems.Thm_HighConfRobust_fact_3_3_iii
-- name    : HighConfRobust.fact_3_3_iii
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:06:59.011322+00:00
-- url     : https://prove2.me/theorems/b5c7bed6-5729-432a-898e-cefbdcef00f5
-- title:
--   Fact 3.3 (iii) — Rényi divergence of two mixtures of the same components
-- statement:
--   Let $H_1,\dots,H_M$ be probability distributions, and let $p=(p_i)_{i\in[M]}$ and $w=(w_i)_{i\in[M]}$ be probability vectors such that $w_i>0$ whenever $p_i>0$. Then for every $q\ge1$,
--
--   $$
--   D_q\Big(\sum_{i=1}^M p_iH_i\,\Big\|\,\sum_{i=1}^M w_iH_i\Big)\le D_q(p\,\|\,w).
--   $$
--
--   The divergence between two mixtures of the same components is at most the divergence between their mixing weights; Lemma 4.3 uses it with three components.
--
--   **Formalization Note** $[M]$ is $\{0,\dots,M-1\}$; the probability vectors take values in the nonnegative extended reals and sum to $1$, and $D_q(p\,\|\,w)$ is the Rényi divergence between the measures $\sum_i p_i\delta_i$ and $\sum_i w_i\delta_i$ on $[M]$.
--
--   Differences from the source:
--   - encoding: probability vectors p, w on [M] and D_q(p ‖ w) → p w : Fin M → ℝ≥0∞ with sum 1, D_q between ∑ p i • dirac i and ∑ w i • dirac i; reason: a probability vector is the same as a probability measure on a finite set
-- source:
--   Narayanan–Lee–Pensia, High Confidence Yields Outlier Robustness, STOC 2027 submission manuscript, Nov. 3, 2026 (sha256 f0e4ec41…c370c153), Fact 3.3 (iii), p.16

import Mathlib
import Definitions.Def_HighConfRobust_renyiDivergence

namespace HighConfRobust

open MeasureTheory

/-- **Fact 3.3 (iii)** (Rényi divergence of mixtures, p.16). Let `H₁, …, H_M` be probability
measures and `p = (p_i)`, `w = (w_i)` probability vectors on `[M]` with `w_i > 0` whenever
`p_i > 0`. Then for every order `q ≥ 1`,
`D_q(∑ᵢ pᵢ Hᵢ ‖ ∑ᵢ wᵢ Hᵢ) ≤ D_q(p ‖ w)`.

Narayanan–Lee–Pensia, *High Confidence Yields Outlier Robustness: Consequences in Computational
Hardness, Privacy, and Replicability*, STOC 2027 submission manuscript, Nov. 3, 2026
(sha256 f0e4ec41…c370c153), Fact 3.3 (iii), p.16.

**Formalization Note** `[M]` is `Fin M`; the probability vectors are `ℝ≥0∞`-valued with sum `1`,
and `D_q(p ‖ w)` is the Rényi divergence between the measures `∑ᵢ pᵢ δᵢ` and `∑ᵢ wᵢ δᵢ` on `Fin M`. -/
theorem fact_3_3_iii {X : Type*} [MeasurableSpace X] {M : ℕ} (H : Fin M → Measure X)
    [∀ i, IsProbabilityMeasure (H i)] (p w : Fin M → ENNReal)
    (hp : ∑ i, p i = 1) (hw : ∑ i, w i = 1) (hpw : ∀ i, p i ≠ 0 → w i ≠ 0)
    (q : ℝ) (hq : 1 ≤ q) :
    renyiDivergence q (∑ i, p i • H i) (∑ i, w i • H i) ≤
      renyiDivergence q (∑ i, p i • Measure.dirac i) (∑ i, w i • Measure.dirac i) := by sorry

end HighConfRobust
