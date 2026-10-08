-- Prove2me | Theorems.Thm_MondererShapley_Participation_hart_mas_colell_step
-- name    : MondererShapley.Participation.hart_mas_colell_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:17:07.794274+00:00
-- url     : https://prove2.me/theorems/8cf86c73-bb17-4449-8ec4-06a39781a27b
-- title:
--   Theorem 6.1, proof — for efficient ψ, (6.3) is solvable iff ψ is the Shapley value on every v_S (Hart–Mas-Colell, Theorem A)
-- statement:
--   Let $\psi$ be an efficient solution and $v \in G(N)$ (so $v(\emptyset) = 0$). Then there is a function $P$ on the coalitions of $N$ with
--
--   $$P(S) - P(S \setminus \{i\}) = \psi(v_{S \cup \{i\}})(i) \qquad \text{for all } S \subseteq N \text{ and every } i \in S$$
--
--   if and only if $\psi$ is the Shapley value on $\{v_S : S \in 2^N\}$, that is, $\psi(v_S)(i) = \varphi_i(v_S)$ for every coalition $S$ and every $i \in S$, where $\varphi(v_S)$ is the Shapley value of the restriction of $v$ to the player set $S$.
--
--   This is the final step of the proof of Theorem 6.1, which the paper takes from Theorem A of Hart and Mas-Colell (1989): a game has a potential whose marginal contributions add up to the worth of every coalition, and those marginal contributions are the Shapley value.
--
--   **Formalization Note** Since $i \in S$, $S \cup \{i\} = S$; the page's $S \cup \{i\}$ is kept on the left. $\psi(v_S)$ is `ψ S v` and $\varphi_i(v_S)$ is `shapleyOn S v i`. Efficiency is assumed for every coalition and every game, as in the paper.
-- source:
--   Monderer and Shapley, Potential Games, Games Econ. Behav. 14 (1996), p. 137 (PDF p. 14), proof of Theorem 6.1, last step (Hart and Mas-Colell 1989, Theorem A)

import Mathlib
import Definitions.Def_MondererShapley_Participation_Solution
import Definitions.Def_MondererShapley_Participation_shapleyOn

namespace MondererShapley.Participation

/-- Theorem 6.1, proof, last step (Hart--Mas-Colell 1989, Theorem A): for an efficient solution
`ψ` and a game `v` with `v ∅ = 0`, a function `P` on coalitions with
`P(S) − P(S∖{i}) = ψ(v_{S∪{i}})(i)` for all `S` and `i ∈ S` exists iff `ψ` is the Shapley value
on every subgame `v_S`. -/
theorem hart_mas_colell_step {ι : Type*} [DecidableEq ι] (ψ : Solution ι) (hψ : IsEfficient ψ)
    (v : Finset ι → ℝ) (hv : v ∅ = 0) :
    (∃ P : Finset ι → ℝ, ∀ S : Finset ι, ∀ i ∈ S, P S - P (S \ {i}) = ψ (S ∪ {i}) v i) ↔
      ∀ S : Finset ι, ∀ i ∈ S, ψ S v i = shapleyOn S v i := by sorry

end MondererShapley.Participation
