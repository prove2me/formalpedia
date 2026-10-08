-- Prove2me | Theorems.Thm_HordijkKallenbergLP_SingleLP_primal_optimal_solution
-- name    : HordijkKallenbergLP.SingleLP.primal_optimal_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:58:11.959859+00:00
-- url     : https://prove2.me/theorems/d6c298ca-309d-4232-993c-69f4e2801f95
-- title:
--   §3.2 (p. 356) — (φ(f₀^∞), D(f₀)r(f₀) + Mφ(f₀^∞)) is primal optimal for M large enough
-- statement:
--   Let $\beta_j>0$, $j\in E$, with $\sum_j\beta_j=1$, and let $f_0^\infty$ be a pure stationary policy that is α-discounted optimal for all α near enough to $1$. There is $c_0$ such that for every $c\ge c_0$ the pair
--   $$\big(\varphi(f_0^\infty),\ D(f_0)r(f_0)+c\,\varphi(f_0^\infty)\big)$$
--   is an optimal solution of the primal program
--   $$\text{minimize }\sum_j\beta_j\tilde\varphi_j\quad\text{subject to }(\tilde\varphi,\tilde u)\text{ superharmonic}.$$
--
--   In particular the primal program has an optimal solution, which the proof of Theorem 7 uses.
--
--   **Formalization Note** "For $M$ large enough" is: there is $c_0$ such that the claim holds for all $c\ge c_0$.
-- source:
--   Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci. 25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 356, §3.2

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_HordijkKallenbergLP_SingleLP_Model
open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter Topology

namespace HordijkKallenbergLP.SingleLP

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- **§3.2, the primal optimal solution.** From the results in §3.1,
`(φ = φ(f₀^∞), u = D(f₀) r(f₀) + M φ(f₀^∞))`, for `M` large enough, is an optimal solution of the
primal linear program `minimize Σ_j β_j φ̃_j` subject to `(φ̃, ũ)` superharmonic, where
`β_j > 0`, `Σ_j β_j = 1` and `f₀^∞` is the policy from Theorem 1.

Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci.
25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 356, §3.2 (unnumbered).

**Formalization Note.** "For `M` large enough" is `∃ c₀, ∀ c ≥ c₀`; the paper's `M` is `c` here.
"The policy from Theorem 1" is the hypothesis `IsDiscOptimalNearOne`. -/
theorem primal_optimal_solution (M : StationaryMDP S A) [Nonempty S]
    (β : S → ℝ) (hβpos : ∀ j, 0 < β j) (hβsum : ∑ j, β j = 1)
    (f₀ : S → A) (hf₀ : ∀ i, f₀ i ∈ M.admissible i) (h₀ : IsDiscOptimalNearOne M f₀ hf₀) :
    ∃ c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c →
      IsPrimalOptimal M β (fun i => gainInf (stationaryPolicy M f₀ hf₀) i)
        (fun i => (deviationMatrix (transMatrix M f₀) *ᵥ rewardVec M f₀) i
          + c * gainInf (stationaryPolicy M f₀ hf₀) i) := by sorry

end HordijkKallenbergLP.SingleLP
