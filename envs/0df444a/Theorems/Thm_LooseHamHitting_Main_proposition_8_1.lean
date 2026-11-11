-- Prove2me | Theorems.Thm_LooseHamHitting_Main_proposition_8_1
-- name    : LooseHamHitting.Main.proposition_8_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:19:49.381566+00:00
-- url     : https://prove2.me/theorems/c752bc16-649a-4738-95f2-3d48bd1b89d6
-- title:
--   Proposition 8.1 — uniform edge-marginal bound q_e(H_j) ≤ C₀(n∗ − s)/(2j) at every state where A_j holds
-- statement:
--   There is an absolute constant $C_0\ge1$ such that, for every choice of parameters and matching satisfying Assumption 4.2, with $P_*$-probability $1-o(1)$, simultaneously for every $m_*\le j\le\binom{n_*}3$ such that $A_j$ holds,
--   $$\max_{e\in H_j}q_e(H_j)\le\frac{C_0(n_*-s)}{2j}.$$
--   The $o(1)$ is a null sequence $\varepsilon(n_*)$, uniform over all parameters and matchings satisfying Assumption 4.2.
--
--   This proposition packages §§9–11 and closes the counting argument of Theorem 4.3.
--
--   Differences from the source:
--   - encoding: with P∗-probability 1 − o(1) → ∃ ε : ℕ → ℝ, ε → 0, with P∗[failure] ≤ ε(n∗) for every instance of Assumption 4.2; reason: explicit null sequence, uniform over the parameters
--   - encoding: edge-deletion process with law P, P∗ = P[· | H_{m∗} ∈ Ω] → uniform ordering of the triples with H_j its first j triples; P∗ as a conditional counting probability; reason: same law of (H_j)
--   - encoding: A_j with log 0 = −∞ → Φ(H_j) > 0 and log Φ(H_j) ≥ L_j − n∗/√log n∗; reason: the −∞ convention; L_j finite once Φ(\binom{[n∗]}{3}) > 0, which holds for all large n∗
-- source:
--   León, Liu, Hitting time for loose Hamilton cycles in the random hypergraph process, arXiv:2610.29894v1, p. 31, Proposition 8.1

import Mathlib
import Definitions.Def_LooseHamHitting_Main_Hypergraph
import Definitions.Def_LooseHamHitting_Main_Process
import Definitions.Def_LooseHamHitting_Main_Core

set_option autoImplicit false

open Classical Filter Topology

namespace LooseHamHitting.Main

/-- Proposition 8.1: with `P∗`-probability `1 − o(1)`, uniformly over all parameters and matchings
satisfying Assumption 4.2, every state `H_j` (`m∗ ≤ j ≤ \binom{n∗}{3}`) at which `A_j` holds has
`max_{e ∈ H_j} q_e(H_j) ≤ C₀ (n∗ − s)/(2j)`. -/
theorem proposition_8_1 :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ (n m : ℕ) (ℓ : Fin n → ℕ) (M₀ : Finset (Finset (Fin n))), CoreAssumption n m ℓ M₀ →
        condProbCore n m ℓ (fun σ => ∃ j : ℕ, m ≤ j ∧ j ≤ n.choose 3 ∧ EventA n M₀ σ j ∧
          MarginalExceeds C₀ n M₀ (prefixGraph σ j) j) ≤ ε n := by sorry

end LooseHamHitting.Main
