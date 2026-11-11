-- Prove2me | Theorems.Thm_IntegerRootsFN_Main_theorem_1_1
-- name    : IntegerRootsFN.Main.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:53:05.813933+00:00
-- url     : https://prove2.me/theorems/7514e029-958e-46aa-bbe1-52928e86ca4f
-- title:
--   Theorem 1.1 — both deterministic integer-root bit complexity bounds
-- statement:
--   Let $n,b\ge1$ be integers and $f(x)=\sum_{j=0}^na_jx^j\in\mathbb Z[x]$ have degree exactly $n$, with $a_n\ne0$ and $|a_j|<2^b$. Coefficients are given as signed binary data; the required output is the complete list of distinct integer roots in binary, without multiplicities. There are two deterministic algorithms, with possibly different finite machines and uniform constants, satisfying respectively
--
--   $$T_a(n,b)=\widetilde O\bigl(nb+\min(n,b)^3b^2\bigr),\qquad T_b(n,b)=\widetilde O(nb).$$
--
--   Both existence assertions occur in one conjunction on the same unrestricted input class. More explicitly, for each branch there are one machine, $C>0$ and fixed natural $k,l$ chosen before every $n,b,f$, such that its halting transition count is at most $CF(n,b)(1+\log_2(n+1))^k(1+\log_2(b+1))^l$, with the corresponding displayed $F$. Each machine must actually halt and write a repetition-free list $R$ satisfying $r\in R$ if and only if $f(r)=0$ for every integer $r$.
--
--   The elementary bound is independent of Pan. The nearly linear branch uses Theorem 3.1 as its supporting proof obligation, with the runtime caveat of Remark 3.2 explicitly retained. No Pan assumption, candidate list, root-set existence, arithmetic oracle or correctness certificate is supplied with an input. Multiple roots, nonreal roots and arbitrary signed leading coefficients are all allowed. This is the full two-clause source theorem, and no square-free or small-height specialization replaces either clause.
--
--   Differences from the source:
--   - encoding: integers n,b≥1 and coefficients given in binary → positive natural parameters, dense signed fixed-width coefficients, finite signed binary outputs; reason: this represents every source input; signs, delimiters, input reads and output writes count as machine steps
--   - encoding: uniform soft-O bit-operation bounds → one finite deterministic multitape machine and positive global C with fixed natural exponents k,l before all varying inputs, bounded by CF(1+log₂(n+1))^k(1+log₂(b+1))^l; reason: shifted logarithms cover the small inputs without changing the allowed polynomial or logarithmic scope; finite initially blank work tapes prohibit advice or assigned costs
-- source:
--   Yansong Feng, Itamar Nir, STOC 2027 submission #1353 (October 2026), p. 2, Theorem 1.1(a),(b); standing assumptions p.2; Remark 3.2 p.8

import Mathlib
import Definitions.Def_IntegerRootsFN_Main_Binary

set_option autoImplicit false

namespace IntegerRootsFN.Main

theorem theorem_1_1 :
    (∃ A : IntMul.MultitapeTM, ∃ C : ℝ, 0 < C ∧ ∃ k l : ℕ,
      ∀ (n b : ℕ) (f : Polynomial ℤ), Valid f n b →
      RootRuns A f n b
        (softBound C k l n b ((n : ℝ) * b + (min n b : ℕ) ^ 3 * (b : ℝ) ^ 2))) ∧
    (∃ B : IntMul.MultitapeTM, ∃ C : ℝ, 0 < C ∧ ∃ k l : ℕ,
      ∀ (n b : ℕ) (f : Polynomial ℤ), Valid f n b →
      RootRuns B f n b (softBound C k l n b ((n : ℝ) * b))) := by sorry

end IntegerRootsFN.Main
