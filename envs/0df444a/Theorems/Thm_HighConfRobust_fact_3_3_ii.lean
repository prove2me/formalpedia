-- Prove2me | Theorems.Thm_HighConfRobust_fact_3_3_ii
-- name    : HighConfRobust.fact_3_3_ii
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:06:56.157167+00:00
-- url     : https://prove2.me/theorems/7138cf2e-367f-4b11-bc8f-a90d18e69e90
-- title:
--   Fact 3.3 (ii) — tensorization of Rényi divergence
-- statement:
--   Let $q\ge1$ and $n\in\mathbb N$, let $P$ and $Q$ be probability distributions on a common space and let $\nu$ be an arbitrary probability distribution (the law of the random seed in the applications). Then
--
--   $$
--   D_q\big(P^{\otimes n}\otimes\nu\,\big\|\,Q^{\otimes n}\otimes\nu\big)=n\,D_q(P\,\|\,Q).
--   $$
--
--   This turns a per-sample divergence bound into a bound for $n$ i.i.d. samples together with an independent seed, which is how Theorem 4.2 handles a randomized algorithm.
--
--   **Formalization Note** $P^{\otimes n}\otimes\nu$ is the product of the $n$-fold product measure on $\mathcal X^n$ with $\nu$. Both sides are extended reals with $0\cdot\infty=0$ and $n\cdot\infty=\infty$ for $n\ge1$; at $n=0$ the left side is $D_q(\nu\,\|\,\nu)=0$.
--
--   Differences from the source:
--   - encoding: n D_q(P ‖ Q) with D_q possibly +∞, n ∈ ℕ → (n : EReal) * renyiDivergence q P Q, with 0 · ⊤ = 0; reason: at n = 0 the left side is D_q(ν ‖ ν) = 0, so 0 · ∞ = 0 is the page's value; no other instance changes
-- source:
--   Narayanan–Lee–Pensia, High Confidence Yields Outlier Robustness, STOC 2027 submission manuscript, Nov. 3, 2026 (sha256 f0e4ec41…c370c153), Fact 3.3 (ii), p.16

import Mathlib
import Definitions.Def_HighConfRobust_renyiDivergence

namespace HighConfRobust

open MeasureTheory

/-- **Fact 3.3 (ii)** (tensorization of Rényi divergence, p.16). For every order `q ≥ 1`, every
`n`, probability measures `P, Q` on a common space and an arbitrary probability measure `ν` (the
law of the random seed),
`D_q(P^{⊗n} ⊗ ν ‖ Q^{⊗n} ⊗ ν) = n · D_q(P ‖ Q)`.

Narayanan–Lee–Pensia, *High Confidence Yields Outlier Robustness: Consequences in Computational
Hardness, Privacy, and Replicability*, STOC 2027 submission manuscript, Nov. 3, 2026
(sha256 f0e4ec41…c370c153), Fact 3.3 (ii), p.16.

**Formalization Note** `P^{⊗n} ⊗ ν` is `(Measure.pi fun _ : Fin n => P).prod ν` on
`(Fin n → X) × Ω`. Both sides are in `EReal`, where `0 · ⊤ = 0` and `n · ⊤ = ⊤` for `n ≥ 1`; at
`n = 0` the left side is `D_q(ν ‖ ν) = 0`. -/
theorem fact_3_3_ii {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (n : ℕ) (q : ℝ) (hq : 1 ≤ q) :
    renyiDivergence q ((Measure.pi fun _ : Fin n => P).prod ν)
        ((Measure.pi fun _ : Fin n => Q).prod ν) =
      (n : EReal) * renyiDivergence q P Q := by sorry

end HighConfRobust
