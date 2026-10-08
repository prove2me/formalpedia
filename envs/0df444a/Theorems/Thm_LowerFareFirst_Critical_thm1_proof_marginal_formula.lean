-- Prove2me | Theorems.Thm_LowerFareFirst_Critical_thm1_proof_marginal_formula
-- name    : LowerFareFirst.Critical.thm1_proof_marginal_formula
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:54:53.088982+00:00
-- url     : https://prove2.me/theorems/47b58f9d-53f4-4b7b-ad51-bd3f455fa2e4
-- title:
--   Proof of Theorem 1, p. 29 — ΔZ_{m̄+1}(k_{m̄+1}+j) = Σ_{i<j} ΔZ_m̄(k_{m̄+1}+j−i)P[D_{m̄+1}=i] + r_{m̄+1}P[D_{m̄+1} ≥ j]
-- statement:
--   Consider the seat management model with lower fare classes booking first under the standing assumptions of §1, with optimal values $Z_m(n)$, marginal seat values $\Delta Z_m(n) = Z_m(n) - Z_m(n-1)$ and critical values $k_m$ from (2b). Let $\bar m$ be a class with $1 \le \bar m$ and $\bar m + 1 \le c$, suppose that $\Delta Z_{\bar m}(n)$ is decreasing (nonincreasing) in $n \ge 1$, and let $k_{\bar m+1}$ be the critical value of class $\bar m + 1$. Then for every $j \ge 1$,
--   $$\Delta Z_{\bar m+1}(k_{\bar m+1}+j) = \sum_{i=0}^{j-1} \Delta Z_{\bar m}(k_{\bar m+1}+j-i)\,P[D_{\bar m+1} = i] + r_{\bar m+1}\,P[D_{\bar m+1} \ge j].$$
--
--   Above the critical value, the marginal seat value for classes $1, \dots, \bar m+1$ is a mixture: if class $\bar m + 1$ brings $i < j$ requests, the $(k_{\bar m+1}+j)$-th seat is worth $\Delta Z_{\bar m}(k_{\bar m+1}+j-i)$ to the higher classes, and if it brings at least $j$ requests, the seat is sold at $r_{\bar m+1}$. The display is the step of the proof of Theorem 1 from which both (6) and the monotonicity of $\Delta Z_{\bar m+1}$ above $k_{\bar m+1} + 1$ follow.
--
--   **Formalization Note.** The page prints $\Delta Z_{\bar m}(k_{\bar m} + j - i)$ inside the sum; the left side and the following display use $k_{\bar m+1}$, and the identity holds only with $k_{\bar m+1}$, which is what is stated here. At $j = 1$ the display is the first identity of Lemma 1, rewritten as a marginal value.
-- source:
--   Wollmer (1992), Operations Research 40(1), proof of Theorem 1, display after "This yields", p. 29

import Mathlib
import Definitions.Def_LowerFareFirst_Critical_Model

namespace LowerFareFirst.Critical

open MeasureTheory

theorem thm1_proof_marginal_formula {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : ℕ → Ω → ℕ) (r : ℕ → ℝ) (c : ℕ)
    (hM : IsSeatModel μ D r c)
    (m k : ℕ) (hm : 1 ≤ m) (hmc : m + 1 ≤ c)
    (hdec : ∀ n : ℕ, 1 ≤ n → dZ μ D r m (n + 1) ≤ dZ μ D r m n)
    (hk : IsCriticalValue μ D r (m + 1) k) :
    ∀ j : ℕ, 1 ≤ j → dZ μ D r (m + 1) (k + j) =
      ∑ i ∈ Finset.range j, dZ μ D r m (k + j - i) * probEq μ D (m + 1) i
        + r (m + 1) * probGe μ D (m + 1) j := by sorry

end LowerFareFirst.Critical
