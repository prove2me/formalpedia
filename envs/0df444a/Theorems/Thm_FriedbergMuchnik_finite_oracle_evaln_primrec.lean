-- Prove2me | Theorems.Thm_FriedbergMuchnik_finite_oracle_evaln_primrec
-- name    : FriedbergMuchnik.finite_oracle_evaln_primrec
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-09T21:00:36.668425+00:00
-- url     : https://prove2.me/theorems/3c1bedec-7f50-4c00-8dc9-3612eacfcbba
-- title:
--   Primitive recursiveness of bounded evaluation for finite-list oracles
-- statement:
--   Let $L$ be an arbitrary finite list of natural numbers and let $O_L(n)$ be $1$ when $n\in L$ and $0$ otherwise. Let $E(L,k,c,n)$ be the option-valued result of the fixed bounded oracle interpreter `oracleEvaln`, using oracle $O_L$, fuel $k\in\mathbb N$, program $c$, and input $n\in\mathbb N$.
--
--   Then the function
--
--   $$ (L,k,c,n)\longmapsto E(L,k,c,n) $$
--
--   is primitive recursive, uniformly in all four arguments, with the existing encodings of lists, programs, products, and optional natural numbers. The result `none` is a legitimate total output of this bounded simulation.
--
--   The statement includes arbitrary lists, with duplicates allowed, fuel zero, and inputs beyond the fuel bound. It assumes no stage invariant, no computability of the priority construction, and no correctness or completeness theorem about unbounded oracle evaluation.
-- source:
--   Arnold W. Miller, Lecture notes in Recursion Theory, December 3, 2008, Section 26, Theorem 26.2, pp. 51–54, https://people.math.wisc.edu/~awmille1/old/m773-07/recthy.pdf#page=52. The construction on p. 52 uses a uniformly bounded finite-oracle simulation; p. 53 asserts effectiveness of the finite-stage sequence. This statement is an elementary, formalization-specific coding lemma for the oracleEvaln interpreter already defined in FriedbergMuchnik_Priority, not a verbatim numbered theorem in Miller. The strengthening to primitive recursiveness is justified by the explicit fuel and input bounds, primitive recursive syntax encoding, and bounded loops.

import Definitions.Def_FriedbergMuchnik_Priority

namespace FriedbergMuchnik

theorem finite_oracle_evaln_primrec :
    Primrec (fun p : List ℕ × (ℕ × (Program × ℕ)) =>
      oracleEvaln (fun n => if n ∈ p.1 then 1 else 0)
        p.2.1 p.2.2.1 p.2.2.2) := by sorry

end FriedbergMuchnik
