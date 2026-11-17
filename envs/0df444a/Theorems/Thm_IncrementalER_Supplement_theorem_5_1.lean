-- Prove2me | Theorems.Thm_IncrementalER_Supplement_theorem_5_1
-- name    : IncrementalER.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:54:22.437407+00:00
-- url     : https://prove2.me/theorems/8261663d-1b44-4a36-82ef-d3f0fad10d3b
-- title:
--   Theorem 5.1 — adaptive one-sided leverage-degree queries
-- statement:
--   Fix quasipolynomial capacity, failure, and polynomial-query regimes. For every connected positive-capacity graph, every real $k>1$, every $0<\varepsilon\le1$, and every $k$-hitting set $S_0$ of size $\widetilde O(m/k)$, uniform preprocessing and query programs support polynomially many adaptive calls `LeverageDegree`$(v,U)$ with $S_0\subseteq U$ and $v\in U\setminus S_0$.
--
--   Every returned estimate is simultaneously one-sided,
--   $$
--   \ell_U^G(v)\le\widehat\ell_U^G(v)\le(1+\varepsilon)\ell_U^G(v),
--   $$
--   with high probability. Initialization uses $\widetilde O(m\operatorname{poly}(k,\varepsilon^{-1}))$ charged work and each query uses $\widetilde O(\operatorname{poly}(k,\varepsilon^{-1}))$ work, even when its set and vertex depend on the full preceding transcript.
--
--   Differences from the source:
--   - encoding: U is passed by pointer to a membership oracle → U is exposed as a random-access characteristic vector and membership is one charged indirect integer-memory load; reason: this is a concrete PNormReg pointer implementation and does not reveal anything beyond membership
--   - encoding: polynomially many adaptive queries with high probability → for each fixed polynomial exponent, every transcript strategy is quantified before the fair-coin failure event, which simultaneously covers all its queries; reason: preserves adaptivity while keeping the adversary independent of future random bits
--   - generalization: graph edges join distinct vertices → edge-list inputs may also contain loops, ignored by all graph quantities; reason: removing loops preserves the source instance and only decreases the size parameter used in upper bounds
-- source:
--   Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, Incremental All-Pairs Effective Resistance in Almost-Linear Time, STOC 2027 submission (manuscript sha256 a0415fd5…), Theorem 5.1, p.29

import Mathlib
import Definitions.Def_IncrementalER_Supplement_theorem51Spec

set_option autoImplicit false

namespace IncrementalER.Supplement

/-- **Theorem 5.1** (Goranci et al., STOC 2027 submission, manuscript sha256 a0415fd5…, p.29).
For every fixed capacity, failure and polynomial-query regime, preprocessing and query programs
answer polynomially many transcript-adaptive membership-oracle queries with the printed one-sided
`(1+epsilon)` guarantee, initialization/query work and one simultaneous high-probability event. -/
theorem theorem_5_1 :
    ∀ A : ℝ, 0 < A → ∀ q : ℕ, ∀ c kappa : ℝ, 1 < c → 0 < kappa →
      ∃ Pre Qry : PNormReg.Program, ∃ C : ℝ, ∃ r p : ℕ,
        A ≤ C ∧ q ≤ r ∧ theorem51Spec Pre Qry C r p c kappa := by sorry

end IncrementalER.Supplement
