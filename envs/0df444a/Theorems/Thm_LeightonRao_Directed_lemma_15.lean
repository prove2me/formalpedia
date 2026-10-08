-- Prove2me | Theorems.Thm_LeightonRao_Directed_lemma_15
-- name    : LeightonRao.Directed.lemma_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:23:27.217821+00:00
-- url     : https://prove2.me/theorems/995836b7-7074-4c2f-9fc6-373519c65a89
-- title:
--   Lemma 15, p. 806 — a set T with |T| ≥ 2n/3 far (in total) from the rest yields a directed cut of ratio cost O(W)
-- statement:
--   Let $G$ be a strongly connected directed network on $n\ge2$ nodes, $d\ge0$ a distance function with total weight $W$, and $T\subseteq V$ with $|T|\ge 2n/3$. If either
--   $$\sum_{u\in V-T}d(T,u)\ge\frac1{4n}\qquad\text{or}\qquad\sum_{u\in V-T}d(u,T)\ge\frac1{4n},$$
--   then there is a nonempty proper $U\subsetneq V$ with
--   $$\frac{C(U,\bar U)}{|U|\,|\bar U|}\le 12\,W.$$
--
--   Here $d(T,u)$ is the shortest directed distance from $T$ to $u$ and $d(u,T)$ the shortest directed distance from $u$ to $T$.
--
--   **Formalization Note** The paper states "ratio cost $O(W)$" and says the proof is virtually identical to Lemma 5's, whose computation (p. 800) gives $R\le 6W$ from the threshold $1/(2n)$; with $1/(4n)$ the same computation gives $12W$, which is the constant stated. Strong connectivity is assumed so that the distances are the paper's (otherwise unreachable pairs would carry Lean's junk value $0$).
-- source:
--   Leighton and Rao, Multicommodity max-flow min-cut theorems and their use in designing approximation algorithms, J. ACM 46 (1999), p. 806, Lemma 15 (proof p. 807, referring to Lemma 5, pp. 799–800)

import Mathlib
import Definitions.Def_LeightonRao_Directed_Setting

namespace LeightonRao.Directed

/-- Leighton–Rao, Lemma 15, p. 806. If `T ⊆ V` has `|T| ≥ 2n/3` and either
`∑_{u ∈ V − T} d(T, u) ≥ 1/(4n)` or `∑_{u ∈ V − T} d(u, T) ≥ 1/(4n)`, then some directed cut has
ratio cost at most `12 W` (the constant of Lemma 5's computation, p. 800, with `1/(4n)` in place of
`1/(2n)`). -/
theorem lemma_15 {V : Type} [Fintype V] [DecidableEq V] (N : DiNetwork V)
    (hn : 2 ≤ Fintype.card V) (hconn : IsStronglyConnectedNet N)
    (d : V → V → ℝ) (hd : ∀ u v, 0 ≤ d u v) (T : Finset V)
    (hT : 2 * (Fintype.card V : ℝ) ≤ 3 * (T.card : ℝ))
    (hsum : 1 / (4 * (Fintype.card V : ℝ)) ≤ ∑ u ∈ Tᶜ, diDistFrom N d T u ∨
      1 / (4 * (Fintype.card V : ℝ)) ≤ ∑ u ∈ Tᶜ, diDistTo N d u T) :
    ∃ U : Finset V, U.Nonempty ∧ Uᶜ.Nonempty ∧ diRatio N U ≤ 12 * diTotalWeight N d := by sorry

end LeightonRao.Directed
