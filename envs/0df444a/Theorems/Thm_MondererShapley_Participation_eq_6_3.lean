-- Prove2me | Theorems.Thm_MondererShapley_Participation_eq_6_3
-- name    : MondererShapley.Participation.eq_6_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:17:07.019353+00:00
-- url     : https://prove2.me/theorems/aea910ad-5a9a-4549-9648-6f5cd481cc48
-- title:
--   (6.3) — with P(ε_S) = Q(ε_S) + Σ_{i∈S} cⁱ, Q satisfies (6.2) iff P(ε_S) − P(ε_{S∖{i}}) = ψ(v_{S∪{i}})(i)
-- statement:
--   Let $\psi$ be a solution, $c \in \mathbb R^N$, $v$ a TU game and $Q : \{0,1\}^N \to \mathbb R$. Define $P$ on coalitions by
--
--   $$P(\varepsilon_S) = Q(\varepsilon_S) + \sum_{i \in S} c^i .$$
--
--   Then $Q$ satisfies (6.2), i.e. $Q(\varepsilon_S) - Q(\varepsilon_{S\setminus\{i\}}) = \psi(v_{S\cup\{i\}})(i) - c^i$ for every $S \subseteq N$ and $i \in S$, if and only if
--
--   $$P(\varepsilon_S) - P(\varepsilon_{S \setminus \{i\}}) = \psi(v_{S \cup \{i\}})(i) \qquad \text{for all } S \subseteq N \text{ and every } i \in S.$$
--
--   The change of variables removes the outside options $c^i$ from the condition, which is why Theorem 6.1 holds for every $c$.
--
--   **Formalization Note** $P$ is a function on coalitions (`Finset ι → ℝ`), $P(S)$ standing for the page's $P(\varepsilon_S)$; $S \mapsto \varepsilon_S$ is a bijection onto $\{0,1\}^N$. The defining relation of $P$ is the hypothesis `hP`.
-- source:
--   Monderer and Shapley, Potential Games, Games Econ. Behav. 14 (1996), p. 137 (PDF p. 14), proof of Theorem 6.1, (6.3)

import Mathlib
import Definitions.Def_MondererShapley_Participation_Solution
import Definitions.Def_MondererShapley_Participation_profileOf

namespace MondererShapley.Participation

/-- (6.3): with `P(ε_S) = Q(ε_S) + ∑_{i∈S} cⁱ`, `Q` satisfies (6.2) iff `P` satisfies
`P(ε_S) − P(ε_{S∖{i}}) = ψ(v_{S∪{i}})(i)` for all `S ⊆ N` and every `i ∈ S`. -/
theorem eq_6_3 {ι : Type*} [DecidableEq ι] (ψ : Solution ι) (c : ι → ℝ)
    (v : Finset ι → ℝ) (Q : (ι → Bool) → ℝ) (P : Finset ι → ℝ)
    (hP : ∀ S : Finset ι, P S = Q (profileOf S) + ∑ i ∈ S, c i) :
    (∀ S : Finset ι, ∀ i ∈ S,
        Q (profileOf S) - Q (profileOf (S \ {i})) = ψ (S ∪ {i}) v i - c i) ↔
      ∀ S : Finset ι, ∀ i ∈ S, P S - P (S \ {i}) = ψ (S ∪ {i}) v i := by sorry

end MondererShapley.Participation
