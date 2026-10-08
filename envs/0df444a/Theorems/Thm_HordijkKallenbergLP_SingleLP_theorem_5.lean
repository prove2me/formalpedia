-- Prove2me | Theorems.Thm_HordijkKallenbergLP_SingleLP_theorem_5
-- name    : HordijkKallenbergLP.SingleLP.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:56:34.370976+00:00
-- url     : https://prove2.me/theorems/4b94de7b-8e84-422f-bb6e-74147db55e39
-- title:
--   Theorem 5 — the two nested optimality equations for φ⁰ = φ(f₀^∞) and u⁰ = D(f₀)r(f₀)
-- statement:
--   Let $f_0^\infty$ be a pure stationary policy that is α-discounted optimal for all α near enough to $1$, let $\varphi^0=\varphi(f_0^\infty)$ and $u^0=D(f_0)r(f_0)$. Then, for every $i\in E$,
--   $$\varphi^0_i=\max_{a\in A(i)}\sum_j p_{iaj}\varphi^0_j,\qquad \varphi^0_i+u^0_i=\max_{a\in A^0(i)}\Big\{r_{ia}+\sum_j p_{iaj}u^0_j\Big\},$$
--   where $A^0(i)=\{a\in A(i)\mid \varphi^0_i=\sum_j p_{iaj}\varphi^0_j\}$.
--
--   These are the multichain average-reward optimality equations, solved by the gain and bias of a Blackwell-optimal policy.
--
--   **Formalization Note** Each maximum is stated as: every action of the index set gives at most the left side, and some action of it attains the left side. In particular $A^0(i)$ is asserted nonempty.
-- source:
--   Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci. 25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 355, Theorem 5

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_HordijkKallenbergLP_SingleLP_Model
open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter Topology

namespace HordijkKallenbergLP.SingleLP

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- **Theorem 5.** Let `f₀^∞` be the policy from Theorem 1, `φ⁰ = φ(f₀^∞)` and
`u⁰ = D(f₀) r(f₀)`. Then `φ⁰_i = max_{a ∈ A(i)} Σ_j p_{iaj} φ⁰_j` and
`φ⁰_i + u⁰_i = max_{a ∈ A⁰(i)} {r_{ia} + Σ_j p_{iaj} u⁰_j}` for `i ∈ E`, where
`A⁰(i) = {a ∈ A(i) | φ⁰_i = Σ_j p_{iaj} φ⁰_j}`.

Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci.
25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 355, Theorem 5.

**Formalization Note.** Each maximum is stated as "every action gives at most the left side, and
some action of the index set attains it"; in particular the second clause asserts that `A⁰(i)` is
nonempty. The first maximum runs over `A(i)` (`M.admissible i`). "The policy from Theorem 1" is
the hypothesis `IsDiscOptimalNearOne`. -/
theorem theorem_5 (M : StationaryMDP S A) [Nonempty S] (f₀ : S → A) (hf₀ : ∀ i, f₀ i ∈ M.admissible i)
    (h₀ : IsDiscOptimalNearOne M f₀ hf₀) :
    let φ0 : S → ℝ := fun i => gainInf (stationaryPolicy M f₀ hf₀) i
    let u0 : S → ℝ := deviationMatrix (transMatrix M f₀) *ᵥ rewardVec M f₀
    (∀ i : S, (∀ a ∈ M.admissible i, ∑ j, M.trans i a j * φ0 j ≤ φ0 i) ∧
        ∃ a ∈ M.admissible i, ∑ j, M.trans i a j * φ0 j = φ0 i) ∧
    (∀ i : S,
        (∀ a ∈ M.admissible i, φ0 i = ∑ j, M.trans i a j * φ0 j →
          M.reward i a + ∑ j, M.trans i a j * u0 j ≤ φ0 i + u0 i) ∧
        ∃ a ∈ M.admissible i, φ0 i = ∑ j, M.trans i a j * φ0 j ∧
          M.reward i a + ∑ j, M.trans i a j * u0 j = φ0 i + u0 i) := by sorry

end HordijkKallenbergLP.SingleLP
