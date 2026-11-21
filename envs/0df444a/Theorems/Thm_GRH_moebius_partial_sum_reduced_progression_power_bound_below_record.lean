-- Prove2me | Theorems.Thm_GRH_moebius_partial_sum_reduced_progression_power_bound_below_record
-- name    : GRH.moebius_partial_sum_reduced_progression_power_bound_below_record
-- status  : Open
-- author  : @mwm
-- created : 2026-11-21T01:14:31.132552+00:00
-- url     : https://prove2.me/theorems/65f2a89e-4377-46fa-baf3-3c37d470200d
-- title:
--   Möbius cancellation in a fixed reduced progression at or below the verified zero-free record
-- statement:
--   Fix a positive modulus $q$, a unit residue class $a \bmod q$, and an exponent $\sigma$ with
--
--   $$
--   \frac{1}{2} < \sigma \le 0.8749570698 .
--   $$
--
--   Then there is a constant $C = C(q,a,\sigma) \ge 0$ such that for every integer $N \ge 0$,
--
--   $$
--   \left|\sum_{\substack{0 \le k \le N \\ k \equiv a \pmod q}} \mu(k)\right| \le C\,(N+1)^{\sigma},
--   $$
--
--   where $\mu$ is the Möbius function and the sum runs over the integers up to $N$ in the fixed reduced class $a$ modulo $q$.
--
--   This is the target estimate [Möbius cancellation up to a sharp cutoff in each reduced residue class](https://prove2.me/theorems/c2e8263f-75e5-4e6c-a57c-32bc7d41e73b) restricted to exponents at or below the verified Dirichlet zero-free boundary $0.8749570698$. The complementary range $\sigma > 0.8749570698$ is already proved unconditionally at [Liouville cancellation in every fixed reduced progression above the current zero-free record](https://prove2.me/theorems/a79a1901-e866-466f-8a5d-5c02b8291dbe), so the two statements together cover exactly the full range $\tfrac12 < \sigma < 1$. Restricting the exponent range makes this statement strictly weaker than the target, and it isolates exactly the cancellation that no currently verified zero-free region supplies.
--
--   The estimate is still open in this restricted range. For $q = 1$ and any fixed $\sigma < 1$ it contains the classical Mertens bound $|M(N)| \ll N^{\sigma}$ with $M(N) = \sum_{k \le N} \mu(k)$; unconditionally no bound of the shape $M(N) \ll N^{\sigma}$ for a fixed $\sigma < 1$ is known. Under GRH the full range holds, with room to spare: L. Ye, Theorem 1.1 gives $M(N;q,a) \ll (N+1)^{1/2}\log^2(qN)$.
--
--   **Formalization Note.** The binders and the conclusion are verbatim the target statement; the single addition is `hcap : σ ≤ 0.8749570698`, the literal complement of the hypothesis `0.8749570698 < σ` used by the above-record theorems, so that the two cases split the exponent range without overlap or gap.
-- source:
--   Restriction of the open Prove2Me theorem https://prove2.me/theorems/c2e8263f-75e5-4e6c-a57c-32bc7d41e73b (GRH.moebius_partial_sum_reduced_progression_power_bound) to exponents sigma <= 0.8749570698. The complementary range sigma > 0.8749570698 is proved at https://prove2.me/theorems/a79a1901-e866-466f-8a5d-5c02b8291dbe (GRH.liouville_reduced_progression_bound_above_record) combined with the square-divisor transfer https://prove2.me/theorems/ed342a94-f581-487e-a655-dd5a9b0ff82e (GRH.moebius_progression_le_of_liouville_progression_le). The unrestricted fixed-modulus estimate is L. Ye, Bounding sums of the Moebius function over arithmetic progressions, Theorem 1.1 (p. 4), https://arxiv.org/pdf/1406.7326 ; for q = 1 it is the classical Mertens bound.

import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped BigOperators

theorem GRH.moebius_partial_sum_reduced_progression_power_bound_below_record
    (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a) (σ : ℝ)
    (hhalf : (1 / 2 : ℝ) < σ) (hone : σ < 1) (hcap : σ ≤ 0.8749570698) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      |∑ k ∈ Finset.range (n + 1),
        if (k : ZMod q) = a then (ArithmeticFunction.moebius k : ℝ) else 0| ≤
          C * ((n : ℝ) + 1) ^ σ := by sorry
