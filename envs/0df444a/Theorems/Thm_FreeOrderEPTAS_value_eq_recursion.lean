-- Prove2me | Theorems.Thm_FreeOrderEPTAS_value_eq_recursion
-- name    : FreeOrderEPTAS.value_eq_recursion
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:28:37.12141+00:00
-- url     : https://prove2.me/theorems/f5d69a58-565e-47cc-a0a4-f1ee5d41cdf2
-- title:
--   p.17 — $V(\sigma)$ is the backward recursion
-- statement:
--   For every permutation $\sigma$:
--
--   1. $V(\sigma)=R_1$;
--   2. the rule "stop at $t$ iff $X_{\sigma(t)}\ge R_{t+1}$" attains this value;
--   3. the program `recursionP` returns $R_1$ at a counted cost of at most $3n$.
--
--   This is the sentence of p.17 that $V(\sigma)$ "can be computed in poly(n) time via dynamic programming".
--
--   Differences from the source:
--   - reading: $V(\sigma)$, "the expected value obtained by an algorithm that utilizes the optimal stopping rule" → the supremum over measurable stopping rules; reason: the operational meaning of the phrase
--   - encoding: poly(n) time → at most $3n$ counted units, with the oracle as one unit each; reason: the cost model of the mission
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, §3.1, p.17

import Mathlib
import Definitions.Def_FreeOrderEPTAS_V
import Definitions.Def_FreeOrderEPTAS_thresholdRule
import Definitions.Def_FreeOrderEPTAS_freeOrder

open MeasureTheory

namespace FreeOrderEPTAS

/-- p.17 (arXiv:2007.13121v3): the value of the optimal stopping rule on `σ` is the backward
recursion, `V(σ) = R_1`, the threshold rule "stop at `t` iff `X_{σ(t)} ≥ R_{t+1}`" attains it, and
the program `recursionP` computes it at a counted cost of at most `3n`. -/
theorem value_eq_recursion {n : ℕ} (I : Instance n) (σ : Equiv.Perm (Fin n)) :
    V I σ = R I σ 0 ∧
      ∫ x, reward (thresholdRule I σ) σ x ∂(Measure.pi I.μ) = R I σ 0 ∧
      ∀ r ∈ ((recursionP (orc I) σ).run 0).support, r.1 = R I σ 0 ∧ r.2.total ≤ 3 * n := by sorry

end FreeOrderEPTAS
