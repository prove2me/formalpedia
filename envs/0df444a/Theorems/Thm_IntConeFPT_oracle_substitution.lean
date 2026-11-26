-- Prove2me | Theorems.Thm_IntConeFPT_oracle_substitution
-- name    : IntConeFPT.oracle_substitution
-- status  : Proved
-- author  : @ohnesorgefelix
-- created : 2026-11-26T13:51:16.594277+00:00
-- url     : https://prove2.me/theorems/88563dbb-cef1-5a5c-8f96-3648c7bd5164
-- title:
--   Oracle substitution — replacing the oracle of an oracle machine by a machine that answers its queries
-- statement:
--   Let $OM$ be an oracle machine and $P$ a machine (both over the alphabet $\{0,1,2,3\}$). There is a machine $W$ with the following property. Suppose that, with oracle $O$, the oracle machine $OM$ maps $x$ to $y$ within $t$ steps, counting each call as one step, and that every query it asks satisfies a predicate $G$. Suppose further that every query $q$ with $G(q)$ has length at most $Q$, and that $P$ maps it to an answer $O(q)$ of length at most $R$ within $T_q\ge0$ steps. Then $W$ maps $x$ to $y$ within
--   $$4\,(t+1)\,(T_q+Q+R+4)$$
--   steps.
--
--   The machine $W$ simulates $OM$ step by step and runs $P$ on its own stacks at every call. It moves the query to the input stack of $P$ and the answer back to the query stack. This gives the familiar fact that an oracle algorithm with polynomially many polynomial-length queries, run with a polynomial-time oracle, is polynomial. The bound is explicit and does not depend on $OM$ or $P$, so it can be combined with time bounds that depend on parameters such as $2^{O(d^2\log(d+1))}$.
--
--   **Formalization Note.** The machine model is the mission's `Machine`/`RunsWithin`, and the oracle model is `IntConeFPT_OracleMachine` (`ORunsWithin`). The answer length $R$ is a separate hypothesis, so moving the answer back does not depend on how many symbols $P$ pushes per step.
-- source:
--   Standard composition of oracle algorithms (e.g. Grötschel–Lovász–Schrijver 1988, §1.2: an oracle-polynomial algorithm with a polynomial-time oracle is polynomial); used in Jansen–Ohnesorge–Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, arXiv:2609.31328 (preprint), proof of Lemma 5, p.35 (Lemma 29 as the separation oracle)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encInt
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_OnlineCRS_Combine_encVec
import Definitions.Def_IntConeFPT_Machine
import Definitions.Def_IntConeFPT_OracleMachine

open OnlineCRS.Combine

namespace IntConeFPT

theorem oracle_substitution (OM : OracleMachine) (P : Machine) :
    ∃ W : Machine, ∀ (O : List Sym → List Sym) (G : List Sym → Prop) (x y : List Sym)
      (t Q R : ℕ) (Tq : ℝ), 0 ≤ Tq →
      ORunsWithin OM O G x y t →
      (∀ q, G q → q.length ≤ Q ∧ (O q).length ≤ R ∧ RunsWithin P q (O q) Tq) →
      RunsWithin W x y (4 * ((t : ℝ) + 1) * (Tq + Q + R + 4)) := by sorry

end IntConeFPT
