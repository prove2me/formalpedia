-- Prove2me | Theorems.Thm_OnlineMaxWeightMatch_Approx_Supplement_theorem_1_1
-- name    : OnlineMaxWeightMatch.Approx.Supplement.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T08:30:37.611069+00:00
-- url     : https://prove2.me/theorems/b98eac18-e0e5-425c-8618-535d74b8fc0e
-- title:
--   Theorem 1.1, p. 1 — approximating the optimal online RideHail value within an absolute constant $\alpha<1$ is PSPACE-hard, also with polynomially bounded data
-- statement:
--   There is an absolute constant $\alpha\in(0,1)$ such that the following hold.
--
--   1. It is PSPACE-hard to compute an $\alpha$-approximation to $OPT_{on}(\mathcal I)$ for RideHail instances $\mathcal I$, that is, a number $a$ with
--   $$\alpha\cdot OPT_{on}(\mathcal I)\le a\le OPT_{on}(\mathcal I).$$
--   2. This remains true when all weights and inverse arrival probabilities are bounded by a polynomial in the size of the input: for some polynomial $q$, the problem stays PSPACE-hard on the instances with positive arrival probabilities and $w_{i,t}\le q(|\mathcal I|)$, $1/p_t\le q(|\mathcal I|)$, where $|\mathcal I|$ is the length of the binary encoding.
--
--   Here $OPT_{on}(\mathcal I)$ is the expected profit of the optimal online algorithm, the benchmark against which Theorem 1.2 (the goal of this mission) gives a polynomial-time $0.51$-approximation. Theorem 1.1 shows that the ratio cannot be pushed to $1$ in polynomial time unless $\mathrm{P}=\mathrm{PSPACE}$.
--
--   **Formalization Note** Instances are finitely presented with rational weights and probabilities. The same $\alpha$ serves both parts. PSPACE-hardness of approximation is a polynomial-time reduction from every PSPACE language with one approximation query (see the definition `ApproxHardness`).
--
--   Differences from the source:
--
--   - reading: "PSPACE-hard to compute an α-approximation" → every PSPACE language reduces to it by a polynomial-time instance map and a polynomial-time decoder that decides membership from any rational α-approximation (ApproxHard); reason: the paper does not fix the reduction notion; its proofs use one query per input (Fact 2.1 and the final rescaling), rational answers give a finite numerical interface, the values of these rational finite instances are rational, and the reductions transform rational answers by rational arithmetic
--   - reading: a RideHail instance as input of a computational problem → finitely presented instances with rational weights w ≥ 0 and probabilities p ∈ [0,1], size = length of their binary encoding; reason: a polynomial-time algorithm reads finite data; real-number inputs have no size
--   - reading: "all weights and inverse arrival probabilities are bounded by some polynomial in the size of the input" → for some polynomial q, hardness on the instances with p_t > 0, w_{i,t} ≤ q(|J|) and 1/p_t ≤ q(|J|), with the same α; reason: an inverse probability is defined only for p_t > 0; the polynomial is fixed for the whole class
-- source:
--   Papadimitriou, Pollner, Saberi & Wajc, Online Stochastic Max-Weight Bipartite Matching: Beyond Prophet Inequalities, arXiv:2102.10261v3, p. 1, Theorem 1.1 (restated p. 6; proof pp. 7–9)

import Mathlib
import Definitions.Def_OnlineMaxWeightMatch_Approx_Supplement_ApproxHardness
import Definitions.Def_OnlineMaxWeightMatch_Approx_Supplement_EncodedRideHail

namespace OnlineMaxWeightMatch.Approx.Supplement

/-- Theorem 1.1: for one absolute constant `α ∈ (0, 1)`, `α`-approximating `OPT_on(I)` is
PSPACE-hard on RideHail instances, and remains so on the instances whose weights and inverse
arrival probabilities are at most `q(|I|)` for some polynomial `q`. -/
theorem theorem_1_1 :
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧
      ApproxHard encRideHail (fun _ => True) ratOptOn α ∧
      ∃ q : Polynomial ℕ, ApproxHard encRideHail (RatRideHail.PolyBounded q) ratOptOn α := by sorry

end OnlineMaxWeightMatch.Approx.Supplement
