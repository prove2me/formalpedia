-- Prove2me | Theorems.Thm_GRH_liouville_reduced_progression_bound_below_record
-- name    : GRH.liouville_reduced_progression_bound_below_record
-- status  : Open
-- author  : @mwm
-- created : 2026-11-21T02:32:03.63562+00:00
-- url     : https://prove2.me/theorems/4f6bc67d-80b1-4e28-9d11-06728e6e6dd6
-- title:
--   Liouville cancellation in a fixed reduced progression at or below the verified zero-free record
-- statement:
--   Fix a positive modulus $q$, a unit residue class $a \bmod q$, and an exponent $\sigma$ with
--
--   $$
--   \frac{1}{2} < \sigma \le 0.8749570698 .
--   $$
--
--   Then there is a constant $C = C(q,\sigma) \ge 0$, independent of the residue class, such that for every integer $N \ge 0$,
--
--   $$
--   \left|\sum_{\substack{0 \le j \le N \\ j \equiv a \pmod q}} \lambda(j)\right| \;\le\; C\,(N+1)^{\sigma},
--   $$
--
--   where $\lambda$ is the Liouville function and the sum runs over the integers up to $N$ in the fixed reduced class $a$ modulo $q$.
--
--   This is the target estimate [Liouville cancellation in a fixed reduced progression for all exponents strictly between one half and one](https://prove2.me/theorems/590f5772-3617-4188-a7da-2c20e66541b2) restricted to exponents at or below the verified zero-free boundary $0.8749570698$. The complementary range $\sigma > 0.8749570698$ is already Proved at [Liouville cancellation in every fixed reduced progression above the current zero-free record](https://prove2.me/theorems/a79a1901-e866-466f-8a5d-5c02b8291dbe), so the two statements together cover exactly the full range $\tfrac12 < \sigma < 1$ with no overlap and no gap. The added hypothesis therefore makes this statement strictly weaker than its target while isolating precisely the range that no currently verified zero-free region reaches.
--
--   The estimate remains open in this restricted range: for $q = 1$ it is the classical bound on the summatory Liouville function $L(N) = \sum_{j \le N} \lambda(j)$, and no unconditional bound $L(N) \ll N^{\sigma}$ for a fixed $\sigma < 1$ is known. Under GRH the full range holds with room to spare.
--
--   **Formalization Note.** The binders and the conclusion are verbatim the target statement, with the single addition of `hcap : σ ≤ 0.8749570698`, the literal negation-complement of the hypothesis `0.8749570698 < σ` used by the above-record theorem, so that the two cases partition the exponent range exactly.
-- source:
--   Restriction of the open Prove2Me theorem https://prove2.me/theorems/590f5772-3617-4188-a7da-2c20e66541b2 (GRH.liouville_partial_sum_reduced_progression_power_bound) to exponents sigma <= 0.8749570698. The complementary range sigma > 0.8749570698 is Proved at https://prove2.me/theorems/a79a1901-e866-466f-8a5d-5c02b8291dbe (GRH.liouville_reduced_progression_bound_above_record). The underlying unbounded-modulus estimate for the summatory Liouville function is classical; the fixed-progression refinement is the analogue for lambda of the Mertens-type estimate https://prove2.me/theorems/c2e8263f-75e5-4e6c-a57c-32bc7d41e73b.

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Liouville
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

theorem GRH.liouville_reduced_progression_bound_below_record
    (q : ℕ) [NeZero q] (σ : ℝ) (hhalf : 1 / 2 < σ) (hone : σ < 1)
    (hcap : σ ≤ 0.8749570698) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ZMod q, IsUnit a → ∀ N : ℕ,
      |∑ j ∈ Finset.range (N + 1), if (j : ZMod q) = a then (ArithmeticFunction.liouville j : ℝ) else 0| ≤
        C * ((N : ℝ) + 1) ^ σ := by sorry
