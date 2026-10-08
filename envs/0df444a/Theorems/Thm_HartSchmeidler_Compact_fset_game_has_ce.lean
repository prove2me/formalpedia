-- Prove2me | Theorems.Thm_HartSchmeidler_Compact_fset_game_has_ce
-- name    : HartSchmeidler.Compact.fset_game_has_ce
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:14:17.955285+00:00
-- url     : https://prove2.me/theorems/f8db3626-191b-450d-9e01-03e834b81c42
-- title:
--   Proof of Theorem 3, p. 24 — every f-set game Γ_T has a correlated equilibrium q_T
-- statement:
--   Let $N$ be any set of players, $S^i$ any strategy sets and $h^i:S\to\mathbb R$ any payoff functions on $S=\prod_jS^j$. Let $T=\prod_iT^i$ be an f-set: every $T^i\subseteq S^i$ is nonempty and finite, and $T^i$ is a singleton for all but finitely many $i$. Then the essentially finite game $\Gamma_T$, in which player $i$ is restricted to $T^i$, has a correlated equilibrium: there are finitely many profiles $s\in F\subseteq T$ and weights $w(s)\ge 0$ with $\sum_{s\in F}w(s)=1$ such that, for every player $i$ and all $r^i,t^i\in T^i$,
--   $$
--   \sum_{s\in F,\ s^i=r^i}w(s)\bigl[h^i(s)-h^i(s^{-i},t^i)\bigr]\ \ge\ 0 .
--   $$
--
--   This is Theorem 1 of the paper applied to $\Gamma_T$; only the finitely many players with $|T^i|\ge 2$ have a nontrivial choice. The equilibria $q_T$ form the net whose cluster point is the correlated equilibrium of Theorem 3.
--
--   **Formalization Note** $q_T$ is encoded by its finite support $F$ and weights $w$ (the predicate `IsFSetCE`). No continuity or topology is needed for this step.
-- source:
--   Hart and Schmeidler, Existence of Correlated Equilibria, Math. Oper. Res. 14 (1989), p. 24, proof of Theorem 3 ("To each f-set T there corresponds an (essentially) finite game"); https://doi.org/10.1287/moor.14.1.18

import Definitions.Def_HartSchmeidler_Compact_Game

namespace HartSchmeidler.Compact

open MeasureTheory

/-- Proof of Theorem 3, p. 24: every f-set game `Γ_T` has a correlated equilibrium `q_T`
(Theorem 1 applied to `Γ_T`), given as finitely many profiles of `T` with weights. -/
theorem fset_game_has_ce {ι : Type*} [DecidableEq ι] {S : ι → Type*}
    (h : ι → Profile S → ℝ) (T : ∀ i, Finset (S i)) (hT : IsFSet T) :
    ∃ (F : Finset (Profile S)) (w : Profile S → ℝ), IsFSetCE h T F w := by sorry

end HartSchmeidler.Compact
