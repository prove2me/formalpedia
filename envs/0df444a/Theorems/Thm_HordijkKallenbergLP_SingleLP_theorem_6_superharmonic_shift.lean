-- Prove2me | Theorems.Thm_HordijkKallenbergLP_SingleLP_theorem_6_superharmonic_shift
-- name    : HordijkKallenbergLP.SingleLP.theorem_6_superharmonic_shift
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:56:28.024731+00:00
-- url     : https://prove2.me/theorems/7888fffa-af66-4756-ac7a-bae06a07babf
-- title:
--   Proof of Theorem 6 (p. 356) — (φ⁰, u⁰ + Mφ⁰) is superharmonic for some real M
-- statement:
--   Let $f_0^\infty$ be a pure stationary policy that is α-discounted optimal for all α near enough to $1$, $\varphi^0=\varphi(f_0^\infty)$ and $u^0=D(f_0)r(f_0)$. Then there is a real number $c$ such that the pair
--   $$\big(\varphi^0,\ u^0+c\,\varphi^0\big)$$
--   is superharmonic: $\varphi^0_i\ge\sum_jp_{iaj}\varphi^0_j$ and $\varphi^0_i+u^0_i+c\varphi^0_i\ge r_{ia}+\sum_jp_{iaj}(u^0_j+c\varphi^0_j)$ for all $a\in A(i)$, $i\in E$.
--
--   This is the first step of the proof of Theorem 6: it exhibits a feasible point of the primal program whose first component is $\varphi^0$.
--
--   **Formalization Note** The paper calls the real number $M$; it is $c$ here because $M$ names the decision process.
-- source:
--   Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci. 25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 356, §3.1, proof of Theorem 6

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_HordijkKallenbergLP_SingleLP_Model
open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter Topology

namespace HordijkKallenbergLP.SingleLP

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- **Proof of Theorem 6, first sentence.** From (1) and (2) it follows that there exists a real
number `M` such that `(φ⁰, u⁰ + M φ⁰)` is superharmonic, where `f₀^∞` is the policy from
Theorem 1, `φ⁰ = φ(f₀^∞)` and `u⁰ = D(f₀) r(f₀)`.

Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci.
25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 356, §3.1, proof of Theorem 6 (unnumbered).

**Formalization Note.** The paper's real number `M` is `c` here (`M` is the decision process).
"The policy from Theorem 1" is the hypothesis `IsDiscOptimalNearOne`. -/
theorem theorem_6_superharmonic_shift (M : StationaryMDP S A) [Nonempty S] (f₀ : S → A)
    (hf₀ : ∀ i, f₀ i ∈ M.admissible i) (h₀ : IsDiscOptimalNearOne M f₀ hf₀) :
    ∃ c : ℝ, Superharmonic M (fun i => gainInf (stationaryPolicy M f₀ hf₀) i)
      (fun i => (deviationMatrix (transMatrix M f₀) *ᵥ rewardVec M f₀) i
        + c * gainInf (stationaryPolicy M f₀ hf₀) i) := by sorry

end HordijkKallenbergLP.SingleLP
