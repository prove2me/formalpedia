-- Prove2me | Theorems.Thm_OnlineRealSampling_Exact_theorem_5_9
-- name    : OnlineRealSampling.Exact.theorem_5_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:12:12.414508+00:00
-- url     : https://prove2.me/theorems/a968276a-6b0f-499c-8988-7d035c4671ff
-- title:
--   Theorem 5.9 — running time with an efficient oracle
-- statement:
--   Let $F$ have a valid oracle whose cost function $C_F$ is efficient with polynomial $g$, let $1\le M\le\Delta$, and let $Z$ be uniform on $\{0,\dots,M-1\}$, independent of the fair bits. The expected running time of Sample$(F,(Z,M),\Delta)$ is
--   $$O\Big(\mathbb E_{X\sim F}\big[C_F(X,\Delta)+\log(X)\,C_F(X,X)\big]\Big),\qquad(41)$$
--   with a constant depending only on $g$.
--
--   The support of $F$ may be countably infinite, and no finite mean is assumed. The bound is applied in each iteration of Theorem 1.2.
--
--   Differences from the source:
--   - encoding: expected values of resources that may be unbounded → lower Lebesgue integrals in [0, ∞], with the resource equal to ∞ on non-termination; reason: no junk value; the same instances, since termination is almost sure
--   - generalization: O(·) bounds for a fixed word size w ≥ 1 → one constant K valid for every word size w ≥ 1; reason: the source's constants do not depend on w; the statement specializes to each fixed w
--   - reading: Word RAM in which big-integer multiplication and division cost O(k log k) or Θ(k²) → concrete charged primitives: addition, subtraction and comparison cost limbs(a)+limbs(b); multiplication and division cost limbs(a)·limbs(b)+limbs(a)+limbs(b); shifts and powers of two cost the limbs of the result plus 1; bit length costs 1; every machine step costs at least 1; reason: the source leaves the multiplication algorithm open and names schoolbook as one option; C_F is assumed to dominate basic arithmetic under either choice
--   - encoding: efficiency (7)–(8) as bounds on quotients → the multiplicative forms; reason: a cost function is positive, so the forms agree
-- source:
--   Draper, Harris & Saad, Online Random Sampling with Real Probabilities, STOC 2027 submission #103, preprint dated 2026-11-02 (source.pdf sha256 66aeb5c181baf97cefba69aa26d29299e888a7a86c837a71af5b77d35f11c3e1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/103.pdf), Theorem 5.9, PDF 14 / printed 13

import Mathlib
import Definitions.Def_OnlineRealSampling_Exact_Algorithms

open MeasureTheory
open scoped ENNReal

namespace OnlineRealSampling.Exact

/-- Theorem 5.9 (efficient oracles). If the oracle's cost function is efficient with polynomial
`g`, the expected running time of `Sample(F, (Z, M), Δ)` is
`O(E_{X∼F}[C_F(X, Δ) + log(X) C_F(X, X)])`, the constant depending only on `g`. -/
theorem theorem_5_9 (g : Polynomial ℝ) :
    ∃ K : ℝ, ∀ w : ℕ, 1 ≤ w → ∀ (O : CDFOracle) (C : ℝ → ℝ → ℝ), O.Valid →
      CostBound w O.toOracleAccess C → Efficient g C →
      ∀ M Δ : ℕ, 1 ≤ M → M ≤ Δ →
        ∫⁻ p, sampleRes w O.toOracleAccess M Δ Usage.time p ∂(stepMeasure M) ≤
          ENNReal.ofReal K *
            ∑' x : ℕ, ENNReal.ofReal (pmf O.F x * (C x Δ + slog x * C x x)) := by sorry

end OnlineRealSampling.Exact
