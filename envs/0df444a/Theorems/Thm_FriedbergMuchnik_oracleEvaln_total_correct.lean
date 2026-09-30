-- Prove2me | Theorems.Thm_FriedbergMuchnik_oracleEvaln_total_correct
-- name    : FriedbergMuchnik.oracleEvaln_total_correct
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-09T21:55:18.710784+00:00
-- url     : https://prove2.me/theorems/53930add-5669-4982-ac98-9cb7cde44ab7
-- title:
--   Soundness and completeness of bounded evaluation with a total oracle
-- statement:
--   Let $O:\mathbb N\to\mathbb N$ be any total oracle, $c$ an oracle program, and $x,y\in\mathbb N$. Write $\operatorname{eval}^{O}(c,x)$ for its partial semantics and $E_k^O(c,x)$ for the existing option-valued bounded interpreter with fuel $k$. Then
--
--   $$
--   \operatorname{eval}^{O}(c,x)\downarrow=y
--   \quad\Longleftrightarrow\quad
--   \exists k\in\mathbb N,\ E_k^O(c,x)=\operatorname{some}(y).
--   $$
--
--   No computability or finite-support hypothesis is imposed on the oracle. The partial semantics receives the total oracle lifted to a partial function. The equivalence includes every program constructor, the interpreter's input guard, and sequential minimization, which fails when an earlier candidate is undefined. This adequacy statement connects bounded stage simulations with convergence relative to a limit oracle.
-- source:
--   Arnold W. Miller, Lecture notes in Recursion Theory, December 3, 2008, Section 26, Theorem 26.2, pp. 51–54, https://people.math.wisc.edu/~awmille1/old/m773-07/recthy.pdf. Definition 26.1 on p. 51 and the bounded computations used on pp. 52–54. This is a formalization-specific adequacy lemma for the already defined oracleEval/oracleEvaln, not a verbatim numbered theorem in Miller. The non-oracle analogue is Nat.Partrec.Code.evaln_sound and evaln_complete in Mathlib/Computability/PartrecCode.lean, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Computability/PartrecCode.lean, lines 655 and 695. Those results concern a different evaluator. The oracle version has a direct Lean proof.

import Definitions.Def_FriedbergMuchnik_Priority

namespace FriedbergMuchnik

theorem oracleEvaln_total_correct (O : ℕ → ℕ) (c : Program) (x y : ℕ) :
    y ∈ oracleEval (PFun.lift O) c x ↔
      ∃ k : ℕ, oracleEvaln O k c x = some y := by sorry

end FriedbergMuchnik
