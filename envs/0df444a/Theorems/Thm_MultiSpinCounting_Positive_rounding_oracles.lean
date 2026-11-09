-- Prove2me | Theorems.Thm_MultiSpinCounting_Positive_rounding_oracles
-- name    : MultiSpinCounting.Positive.rounding_oracles
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:22:55.5812+00:00
-- url     : https://prove2.me/theorems/115d509d-83e0-41e6-beb0-69938a123d3c
-- title:
--   §2.4, (2.2) — outward rounding, bit cost and output length
-- statement:
--   For every precision $P\ge3$, the outward-rounding functions satisfy, for every real $x>0$,
--   $$0<\operatorname{round}_P^-(x)\le x\le\operatorname{round}_P^+(x),\qquad \max\{\log(x/\operatorname{round}_P^-(x)),\log(\operatorname{round}_P^+(x)/x)\}\le2^{2-P}.$$
--   There are an absolute positive constant $C$ and one finite deterministic bit machine, both chosen before $P$ and the input, computing both rounded values for positive rational $x$ in at most $C(\operatorname{bit}(x)+P)^2$ steps. If rational endpoints $0<l\le x\le u$ each have at most $L$ bits, each rounded value has at most $C(L+P)$ bits, including for real $x$.
--
--   This is the analytic and bit-complexity interface for outward rounding, with every clause of §2.4 retained.
--
--   Differences from the source:
--   - encoding: binary rational data and bit operations → published binary serializers and a finite-stack FinTM2 machine, with time witnessed by TM2OutputsInTime; reason: the encoder only serializes input data; all stacks, control and program labels are finite, and a fixed macro cost is absorbed in the constant
--   - encoding: O(·) with an absolute implicit constant → one positive natural constant chosen before all inputs and dimensions; reason: the finitely many small encoding sizes are absorbed in this constant; no input is excluded
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #268 (October 2026), p. 9, §2.4 and (2.2)

import Mathlib
import Definitions.Def_MultiSpinCounting_Positive_Rounding

namespace MultiSpinCounting.Positive
open OnlineCRS.Combine

/-- All clauses of §2.4 and (2.2), p. 9; constants are uniform even in P. -/
theorem rounding_oracles :
    ∃ (C : ℕ) (M : BitMachine), 0 < C ∧
      (∀ (P : ℕ), 3 ≤ P → ∀ x : ℚ, 0 < x →
        ∃ m : ℕ, Runs M (encRoundingInput P x) (encRoundingOutput P (x : ℝ)) m ∧
          m ≤ C * ((encRat x).length + P)^2) ∧
      (∀ (P : ℕ), 3 ≤ P → ∀ (x : ℝ) (l u : ℚ) (L : ℕ),
        0 < l → (l : ℝ) ≤ x → x ≤ (u : ℝ) →
        (encRat l).length ≤ L → (encRat u).length ≤ L →
        (encRat (roundDown P x)).length ≤ C*(L+P) ∧
        (encRat (roundUp P x)).length ≤ C*(L+P)) ∧
      (∀ (P : ℕ), 3 ≤ P → ∀ x : ℝ, 0 < x →
        0 < (roundDown P x : ℝ) ∧ (roundDown P x : ℝ) ≤ x ∧ x ≤ (roundUp P x : ℝ) ∧
        max (Real.log (x / (roundDown P x : ℝ)))
          (Real.log ((roundUp P x : ℝ) / x)) ≤ roundingAccuracy P) := by sorry

end MultiSpinCounting.Positive
