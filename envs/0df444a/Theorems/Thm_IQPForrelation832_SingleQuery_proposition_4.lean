-- Prove2me | Theorems.Thm_IQPForrelation832_SingleQuery_proposition_4
-- name    : IQPForrelation832.SingleQuery.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T03:07:40.242578+00:00
-- url     : https://prove2.me/theorems/9ddd1b90-46da-4586-9404-08d4fb8edeba
-- title:
--   Proposition 4 — quadratic Boolean polarization
-- statement:
--   For every natural dimension $n$ and every $x,y\in V_n$, let $Q(x)=\sum_{i<j}x_ix_j$ and let $|x|$ be the integer Hamming weight. Then
--   $$
--   Q(x)+Q(y)+Q(x+y)=x\cdot y+|x||y|\pmod2.
--   $$
--   This identity identifies the precise parity correction to bilinearity. In Lean the equation is in $\mathbb F_2$, so the congruence is literal equality after casting the Hamming weights.
--
--   Differences from the source:
--   - encoding: binary strings and real sign-valued functions → Cube n = Fin n → ZMod 2 and real functions with an explicit IsSign predicate; reason: the coordinatewise Bool equivalence preserves every string, XOR, pairing and sign value, including dimension zero
--   - encoding: integer quadratic sums compared modulo two → Q is directly computed in ZMod 2; reason: reduction commutes with these finite additions and products, so no congruence information is lost
-- source:
--   Quentin Buzet, André Chailloux, IQP circuits for 2-Forrelation, STOC 2027 submission #832 (October 2026), p. 16, Proposition 4. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/832.pdf

import Definitions.Def_IQPForrelation832_SingleQuery_Programs

set_option autoImplicit false

namespace IQPForrelation832.SingleQuery

theorem proposition_4 (n : ℕ) (x y : Cube n) :
    Q x + Q y + Q (x+y) = dot x y + (weight x : ZMod 2) * (weight y : ZMod 2) := by sorry

end IQPForrelation832.SingleQuery
