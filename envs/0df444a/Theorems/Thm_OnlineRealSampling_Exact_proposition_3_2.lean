-- Prove2me | Theorems.Thm_OnlineRealSampling_Exact_proposition_3_2
-- name    : OnlineRealSampling.Exact.proposition_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:11:52.717145+00:00
-- url     : https://prove2.me/theorems/61ec4a69-5012-4c5d-9583-c44c373ba042
-- title:
--   Proposition 3.2 — EstimatePMF
-- statement:
--   Let $F$ be a CDF with a valid oracle, $C_F$ a cost function of the oracle, $x\in\mathbb N$, $\nu\ge1$ an integer, and $p=f(x)$.
--   1. If $p=0$, EstimatePMF$(F,x,\nu)$ never returns.
--   2. If $p>0$, it returns $\hat p$ with $\hat p\le p\le(1+1/\nu)\hat p$, using at most $K\log(\nu/p)$ oracle calls and at most $K\log(\nu/p)$ big-integer arithmetic operations, in word-RAM time at most
--   $$K\,\log(\nu/p)\,C_F(x,8\nu/p).$$
--
--   Here $\log$ is the clamped logarithm and $K$ is an absolute constant. The estimate is used once per call of Sample, to choose how far Recycle rescales the output interval.
--
--   Differences from the source:
--   - encoding: the returned estimate p̂ → p̂ = u / 2^{j+1} for the returned numerator u at the final loop index j; reason: the rational value of the returned F⁻(x,j) − F⁺(x−1,j)
--   - encoding: call and operation counts with no cost function in the hypotheses → a cost function C_F of the oracle is assumed for all clauses; reason: every oracle admits a cost function (see the Machine definition), so the hypothesis excludes no instance
--   - generalization: O(·) bounds for a fixed word size w ≥ 1 → one constant K valid for every word size w ≥ 1; reason: the source's constants do not depend on w; the statement specializes to each fixed w
--   - reading: Word RAM in which big-integer multiplication and division cost O(k log k) or Θ(k²) → concrete charged primitives: addition, subtraction and comparison cost limbs(a)+limbs(b); multiplication and division cost limbs(a)·limbs(b)+limbs(a)+limbs(b); shifts and powers of two cost the limbs of the result plus 1; bit length costs 1; every machine step costs at least 1; reason: the source leaves the multiplication algorithm open and names schoolbook as one option; C_F is assumed to dominate basic arithmetic under either choice
-- source:
--   Draper, Harris & Saad, Online Random Sampling with Real Probabilities, STOC 2027 submission #103, preprint dated 2026-11-02 (source.pdf sha256 66aeb5c181baf97cefba69aa26d29299e888a7a86c837a71af5b77d35f11c3e1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/103.pdf), Proposition 3.2, PDF 8 / printed 7; Algorithm 5 and proof in Appendix B, PDF 20 / printed 19

import Mathlib
import Definitions.Def_OnlineRealSampling_Exact_Algorithms

open MeasureTheory
open scoped ENNReal

namespace OnlineRealSampling.Exact

/-- Proposition 3.2 (EstimatePMF). For a valid CDF oracle, `x ≥ 0` and `ν ≥ 1`, with
`p = f(x)`: if `p = 0` the algorithm never returns; if `p > 0` it returns `p̂` with
`p̂ ≤ p ≤ (1 + 1/ν) p̂`, using `O(log(ν/p))` oracle calls and arithmetic operations and
`O(log(ν/p) C_F(x, 8ν/p))` word time. -/
theorem proposition_3_2 :
    ∃ K : ℝ, ∀ w : ℕ, 1 ≤ w → ∀ (O : CDFOracle) (C : ℝ → ℝ → ℝ), O.Valid →
      CostBound w O.toOracleAccess C → ∀ x ν : ℕ, 1 ≤ ν → ∀ ω : ℕ → Bool,
        (pmf O.F x = 0 → ¬ (estimatePMF w).Halts O.toOracleAccess w ω (EstState.init x ν)) ∧
        (0 < pmf O.F x → ∃ c : Config EstState,
          (estimatePMF w).run O.toOracleAccess w ω (EstState.init x ν) = some c ∧
          c.st.estimate ≤ pmf O.F x ∧ pmf O.F x ≤ (1 + 1 / (ν : ℝ)) * c.st.estimate ∧
          (c.calls : ℝ) ≤ K * slog (ν / pmf O.F x) ∧
          (c.ops : ℝ) ≤ K * slog (ν / pmf O.F x) ∧
          (c.time : ℝ) ≤ K * slog (ν / pmf O.F x) * C x (8 * ν / pmf O.F x)) := by sorry

end OnlineRealSampling.Exact
