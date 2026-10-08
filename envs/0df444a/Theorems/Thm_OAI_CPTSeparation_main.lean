-- Prove2me | Theorems.Thm_OAI_CPTSeparation_main
-- name    : OAI.CPTSeparation.main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:25.832071+00:00
-- url     : https://prove2.me/theorems/9c2089af-9d48-4714-a7ef-06fc23d1c1c5
-- statement:
--   The theorem states that a conjunction of three facts holds about a query on finite structures with binary relations over scalars in Z/3. An input on a finite type A assigns to each of the symbols Ed, Cf, EB, VB, I and Z(δ), for δ in Z/3, a Boolean binary relation on A. Its edges are the points y with Ed(y,y), and its configurations are the points a with Cf(a,a). The coefficient of an edge y and configuration a is the sum, over edges x with I(a,x), of the sum of those δ for which Z(δ)(y,x) holds. A configuration t is incident to an edge y when some configuration a with VB(t,a) and some edge x with I(a,x) satisfy EB(y,x). A function λ on configurations is normalized if for every configuration t the sum of λ(a) over configurations a with VB(t,a) equals 1; a pair (λ, μ), with μ a Z/3-valued function on edges, is consistent if for every incident pair (t,y), μ(y) equals the sum over a with VB(t,a) of λ(a) times the coefficient of y and a. The query holds when some normalized λ and some μ are consistent. The first conjunct says the query is invariant under isomorphism, meaning a bijection between the underlying finite types that preserves every relation. The second, OrdinaryPolynomialTime, says there is a Boolean function on ordered inputs (N, relation tables on Fin N) and a polynomial-time multi-stack Turing machine, with a finite alphabet on each stack, computing it from the encoding (N blank letters, a separator 0, then the 8N² table bits), such that for every finite A, every bijection e from A to Fin N and every input S, the function accepts the table of S transported along e exactly when the query holds for S. The third conjunct says the query is not evaluation-definable in the full choiceless polynomial time model: no program with finitely many dynamic functions, whose body is a parallel update rule over hereditarily finite sets built from the atoms, and no polynomial time bound and space bound in |A| exist such that, for every finite input, the program accepts within the time bound with a halted, accepting state and at most the space bound many occurring hereditarily finite sets, exactly when the query holds.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ChoicelessPolynomialTime.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ChoicelessPolynomialTime.lean; bytes 19291..19532
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_ChoicelessPolynomialTime

namespace OAI

noncomputable section

universe uA uB uC uF uR

namespace CPTSeparation

theorem main :
    (∀ (A B : Type) [Fintype A] [Fintype B] (S : Input A) (T : Input B),
      S.Iso T → (S.query ↔ T.query)) ∧
    OrdinaryPolynomialTime ∧
    ¬ FullCPT.EvaluationDefinable (fun {_} [_] I => I.query) := by
  sorry

end CPTSeparation
end
end OAI
