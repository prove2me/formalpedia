-- Prove2me | Theorems.Thm_HighConfRobust_fact_4_4
-- name    : HighConfRobust.fact_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:06:58.359201+00:00
-- url     : https://prove2.me/theorems/72f57c40-a2c2-43b8-a0a7-5bda4323ad06
-- title:
--   Fact 4.4 — Rényi divergence of the ternary weight vectors is at most $2\varepsilon/\kappa$
-- statement:
--   Let $\varepsilon\in(0,1]$ and $a\in(0,1)$, and set
--
--   $$
--   \lambda=\min(1,a/\varepsilon),\qquad \kappa=\frac{1}{\max(1,\log(\varepsilon/a))},\qquad q=1+\kappa .
--   $$
--
--   For the probability vectors on three points
--
--   $$
--   w=\big(1-\varepsilon,\ \varepsilon(1-\lambda),\ \lambda\varepsilon\big),\qquad w'=\big(1-\varepsilon,\ 0,\ \varepsilon\big),
--   $$
--
--   we have
--
--   $$
--   D_q(w'\,\|\,w)\le\frac{2\varepsilon}{\kappa}.
--   $$
--
--   These are the weights of the contaminated law $Q$ and of the reference law $F$ over the three components $P_0,H_1,H_2$ in the proof of Lemma 4.3; with Fact 3.3 (iii) this bounds $D_q(Q\,\|\,F)$.
--
--   **Formalization Note** The ternary vectors are the measures $\sum_i w_i\delta_i$ on a three-point set. The page states the fact "following the notation above", i.e. in the proof of Lemma 4.3, whose ranges $\varepsilon\in(0,1]$, $a\in(0,1)$ are made explicit here.
--
--   Differences from the source:
--   - encoding: "following the notation above" (w, w′, λ, κ, q, ε, a of the proof of Lemma 4.3) → w, w′, λ, κ defined in the statement; ε ∈ (0, 1], a ∈ (0, 1) as hypotheses; vectors as ∑ wᵢ • dirac i on Fin 3; reason: makes the inherited notation and ranges explicit; same instances
-- source:
--   Narayanan–Lee–Pensia, High Confidence Yields Outlier Robustness, STOC 2027 submission manuscript, Nov. 3, 2026 (sha256 f0e4ec41…c370c153), Fact 4.4, p.18 (notation of the proof of Lemma 4.3, p.17)

import Mathlib
import Definitions.Def_HighConfRobust_renyiDivergence

namespace HighConfRobust

open MeasureTheory

/-- **Fact 4.4** (Rényi divergence of ternary measures, p.18), in the notation of the proof of
Lemma 4.3 (p.17). Let `ε ∈ (0, 1]`, `a ∈ (0, 1)`, `λ = min(1, a/ε)`, `κ = 1 / max(1, log(ε/a))`
and `q = 1 + κ`. For the probability vectors on three points
`w = (1 − ε, ε(1 − λ), λε)` and `w' = (1 − ε, 0, ε)`, `D_q(w' ‖ w) ≤ 2ε/κ`.

Narayanan–Lee–Pensia, *High Confidence Yields Outlier Robustness: Consequences in Computational
Hardness, Privacy, and Replicability*, STOC 2027 submission manuscript, Nov. 3, 2026
(sha256 f0e4ec41…c370c153), Fact 4.4, p.18 (notation from the proof of Lemma 4.3, p.17).

**Formalization Note** The ternary vectors are the measures `∑ᵢ wᵢ δᵢ` on `Fin 3` with weights
`ENNReal.ofReal` of the stated reals; the ranges of `ε` and `a` are those of Lemma 4.3. -/
theorem fact_4_4 (ε a : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (ha : 0 < a) (ha1 : a < 1) :
    let lam : ℝ := min 1 (a / ε)
    let κ : ℝ := 1 / max 1 (Real.log (ε / a))
    let w : Fin 3 → ENNReal :=
      ![ENNReal.ofReal (1 - ε), ENNReal.ofReal (ε * (1 - lam)), ENNReal.ofReal (lam * ε)]
    let w' : Fin 3 → ENNReal := ![ENNReal.ofReal (1 - ε), 0, ENNReal.ofReal ε]
    renyiDivergence (1 + κ) (∑ i, w' i • Measure.dirac i) (∑ i, w i • Measure.dirac i) ≤
      ((2 * ε / κ : ℝ) : EReal) := by sorry

end HighConfRobust
