-- Prove2me | Theorems.Thm_FullForesight_Randomized_proposition_1
-- name    : FullForesight.Randomized.proposition_1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-10T06:16:47.414736+00:00
-- url     : https://prove2.me/theorems/5f0ae681-8d4d-4a61-977b-f65b96959b8b
-- title:
--   Proposition 1 — $\Psi$ has a unique root $\xi^\star \approx 0.7941970147$ in $(1/2, 1)$
-- statement:
--   Let $\Psi(\xi) = 89\xi^4 - 44\xi^3 - 19\xi^2 - 3\xi + 1$ and let $\xi^\star$ be the root of $\Psi$ in $(1/2,1)$ as defined (the supremum of the roots in $[1/2, 1]$). Then $\xi^\star$ lies in $(1/2, 1)$, $\Psi(\xi^\star) = 0$, it is the only root of $\Psi$ in $(1/2, 1)$, and
--   $$0.7941970146 < \xi^\star < 0.7941970148 .$$
--
--   This makes the threshold $\xi^\star$ of Main Result 1 well defined (Appendix A.1).
--
--   Differences from the source:
--   - reading: "$\xi^\star \approx 0.7941970147$" → $0.7941970146 < \xi^\star < 0.7941970148$; reason: the enclosure the proof itself establishes (p. 19), giving the ≈ an explicit meaning.
--   - encoding: "a unique root $\xi^\star$" → $\xi^\star$ is a concrete definition (supremum of the roots in $[1/2,1]$) and the conclusion asserts that it is a root in $(1/2,1)$ and the only one there; reason: a defined constant needs its defining property in the conclusion; the claims are those of the proposition.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission (sha256 ef7bb5aa…), p. 18, Proposition 1 (enclosure from its proof, p. 19)

import Mathlib
import Definitions.Def_FullForesight_Randomized_Constants

namespace FullForesight.Randomized

theorem proposition_1 :
    (1 / 2 : ℝ) < xiStar ∧ xiStar < 1 ∧ Psi xiStar = 0 ∧
      (∀ ξ ∈ Set.Ioo (1 / 2 : ℝ) 1, Psi ξ = 0 → ξ = xiStar) ∧
      (0.7941970146 : ℝ) < xiStar ∧ xiStar < 0.7941970148 := by sorry

end FullForesight.Randomized
