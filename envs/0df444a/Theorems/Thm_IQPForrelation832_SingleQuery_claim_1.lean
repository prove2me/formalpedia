-- Prove2me | Theorems.Thm_IQPForrelation832_SingleQuery_claim_1
-- name    : IQPForrelation832.SingleQuery.claim_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T03:07:49.054644+00:00
-- url     : https://prove2.me/theorems/3bf3a3a6-f8be-4bc9-b022-64c08229a3f4
-- title:
--   Claim 1 (corrected: dimension-zero parity sums)
-- statement:
--   For every natural dimension $n$ and $x\in V_n$, let $S(x)$ be the sum of $(-1)^{x\cdot y}$ over all $y$, and let $S_{\rm even}(x)$ and $S_{\rm odd}(x)$ restrict that sum to the indicated Hamming-weight parity. With $0^n$ and $1^n$ denoting the two constant vectors,
--   $$
--   S(x)=2^n[x=0^n],\quad
--   S_{\rm even}(x)=\frac{2^n}{2}([x=0^n]+[x=1^n]),\quad
--   S_{\rm odd}(x)=\frac{2^n}{2}([x=0^n]-[x=1^n]).
--   $$
--   All three identities are retained in one item. The parity identities correct only the zero-dimensional boundary and provide the orthogonality facts used by the acceptance calculation.
--
--   Differences from the source:
--   - correction: even character sum 2^(n-1) at zero or one and overlapping odd-sum branches → 2^n/2 times the sum or difference of the two endpoint indicators; reason: at n=0 the unique vector is both zero and one and the actual sums are 1,1,0; the printed even value is 1/2 and the odd first-branch value is 1/2; all positive-dimensional instances are unchanged
--   - encoding: binary strings and real sign-valued functions → Cube n = Fin n → ZMod 2 and real functions with an explicit IsSign predicate; reason: the coordinatewise Bool equivalence preserves every string, XOR, pairing and sign value, including dimension zero
-- source:
--   Quentin Buzet, André Chailloux, IQP circuits for 2-Forrelation, STOC 2027 submission #832 (October 2026), p. 12, Claim 1. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/832.pdf

import Definitions.Def_IQPForrelation832_SingleQuery_Programs

set_option autoImplicit false

namespace IQPForrelation832.SingleQuery

/-- Claim 1, with only the dimension-zero parity formulas corrected. -/
theorem claim_1 (n : ℕ) (x : Cube n) :
    (∑ y, character x y) = (if x = 0 then (2 : ℝ)^n else 0) ∧
    (∑ y, if Even (weight y) then character x y else 0) =
      (2 : ℝ)^n / 2 * ((if x = 0 then 1 else 0) + (if x = 1 then 1 else 0)) ∧
    (∑ y, if Odd (weight y) then character x y else 0) =
      (2 : ℝ)^n / 2 * ((if x = 0 then 1 else 0) - (if x = 1 then 1 else 0)) := by sorry

end IQPForrelation832.SingleQuery
