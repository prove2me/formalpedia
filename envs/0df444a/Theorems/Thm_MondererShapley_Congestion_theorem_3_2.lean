-- Prove2me | Theorems.Thm_MondererShapley_Congestion_theorem_3_2
-- name    : MondererShapley.Congestion.theorem_3_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:17:23.746994+00:00
-- url     : https://prove2.me/theorems/aecb41f6-33c7-4630-95c7-df211ad9c50c
-- title:
--   Theorem 3.2 — every finite potential game is isomorphic to a congestion game
-- statement:
--   Let $\Gamma$ be a finite potential game: finitely many players $N$, finite strategy sets $Y^i$, payoff functions $u^i : Y \to \mathbb{R}$, and an exact potential $P$ for $\Gamma$. Then there are a finite facility set $M = \{1, \dots, m\}$ and a congestion model $C(N, M, (\Sigma^i)_{i\in N}, (c_j)_{j\in M})$ in which every strategy $A^i \in \Sigma^i$ is a nonempty set of facilities, such that $\Gamma$ is isomorphic to the associated congestion game: there are bijections $g^i : Y^i \to \Sigma^i$ with
--
--   $$u^i(y^1, \dots, y^n) = v^i\big(g^1(y^1), \dots, g^n(y^n)\big) \qquad \text{for every } i \in N \text{ and every } (y^1, \dots, y^n) \in Y,$$
--
--   where $v^i(A) = \sum_{j\in A^i} c_j(\sigma_j(A))$ is the congestion payoff (3.1).
--
--   Together with Theorem 3.1 (every congestion game is a potential game, a result of Rosenthal), this identifies the finite potential games with the congestion games up to isomorphism.
--
--   **Formalization Note.** The facility set is `Fin m` for some natural number $m$ (the paper's $M = \{1,\dots,m\}$). The congestion model is the published `CongestionPoA.AsymSum.CongestionGame`, whose `latency j k` is the paper's $c_j(k)$ (an arbitrary real number; values at $k = 0$ and $k > n$ are never used). The nonemptiness of every strategy, required by the definition of a congestion model on p. 133 but not by the published structure, is a separate conjunct. Since the bijections land on the subtype of `G.strategies i`, the strategies of each player are distinct facility sets. No nonemptiness of the strategy sets and no lower bound on the number of players is assumed: the theorem holds for one player as well.
-- source:
--   Monderer and Shapley, Potential Games, Games Econ. Behav. 14 (1996), p. 133 (PDF p. 10), Theorem 3.2; proof in Appendix B, pp. 140–141

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model
import Definitions.Def_MondererShapley_ClosedPath_IsPotentialGame
import Definitions.Def_MondererShapley_Congestion_IsIsomorphic
import Definitions.Def_MondererShapley_Congestion_congestionPayoff

open CongestionPoA.AsymSum

namespace MondererShapley.Congestion

/-- Monderer and Shapley (1996), p. 133, Theorem 3.2: every finite potential game is isomorphic to a
congestion game. The congestion game has facility set `M = {1, …, m}` (`Fin m`), every strategy of
every player is a nonempty set of facilities, and the bijections `gⁱ` map `Yⁱ` onto the strategy
sets `Σⁱ`. -/
theorem theorem_3_2 {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : ι → Type*} [∀ i, Fintype (Y i)]
    (u : ι → (∀ i, Y i) → ℝ) (hu : MondererShapley.ClosedPath.IsPotentialGame u) :
    ∃ (m : ℕ) (G : CongestionGame ι (Fin m)),
      (∀ i, ∀ A ∈ G.strategies i, A.Nonempty) ∧ IsIsomorphic u (congestionPayoff G) := by sorry

end MondererShapley.Congestion
