-- Prove2me | Theorems.Thm_FriedbergMuchnik_oracle_programs_exact
-- name    : FriedbergMuchnik.oracle_programs_exact
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-09T20:04:07.300178+00:00
-- url     : https://prove2.me/theorems/88b69003-30b1-4d93-9b1c-5e98e17de669
-- title:
--   Oracle programs exactly capture relative partial recursiveness
-- statement:
--   Let $O,f:\mathbb N\rightharpoonup\mathbb N$ be arbitrary partial functions. Let $\operatorname{eval}^{O}(c)$ denote the partial function interpreted from an oracle program $c$ in the imported language. Then
--
--   $$f\text{ is partial recursive relative to }O\quad\Longleftrightarrow\quad\exists c,\ \operatorname{eval}^{O}(c)=f.$$
--
--   The programs use oracle queries, successor, pairing projections, pairing, composition, primitive recursion, and minimization from zero. The constant-zero function is expressible within this language. Equality is equality of partial functions, including their domains; no totality assumption is imposed on $O$ or $f$.
--
--   This equivalence connects explicit program requirements to Mathlib's `RecursiveIn` and hence to the mission's Turing-reducibility predicate.
-- source:
--   Formalization bridge for the oracle programs in Arnold W. Miller, Lecture notes in Recursion Theory, December 3, 2008, Section 26, Theorem 26.2, pp. 51–54, https://people.math.wisc.edu/~awmille1/old/m773-07/recthy.pdf#page=51; semantics follows Mathlib Nat.RecursiveIn and RecursiveIn.iff_nat, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Computability/RecursiveIn.lean. Program-tree encoding is transported from Nat.Partrec.Code, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Computability/PartrecCode.lean.

import Definitions.Def_FriedbergMuchnik_Priority

namespace FriedbergMuchnik

theorem oracle_programs_exact (O f : ℕ →. ℕ) :
    RecursiveIn {O} f ↔ ∃ c : Program, oracleEval O c = f := by sorry

end FriedbergMuchnik
