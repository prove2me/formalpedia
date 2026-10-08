-- Prove2me | Theorems.Thm_LeightonRao_Directed_theorem_12
-- name    : LeightonRao.Directed.theorem_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:23:38.982487+00:00
-- url     : https://prove2.me/theorems/8f61b0d7-76b7-45fc-abb9-5785b5c3901b
-- title:
--   Theorem 12, p. 804 — for every directed uniform multicommodity flow problem, Ω(𝒮/log n) ≤ f ≤ 𝒮
-- statement:
--   There is an absolute constant $c>0$ such that for every directed network $G$ on $n\ge2$ nodes, the max-flow $f$ and the min-cut $\mathcal S$ of its directed uniform multicommodity flow problem (demand $1$ from $u$ to $v$ for every ordered pair $u\ne v$) satisfy
--   $$c\,\frac{\mathcal S}{\log n}\le f\le\mathcal S,$$
--   $\log$ to base $2$. Here $\mathcal S=\min_{\emptyset\ne U\subsetneq V}C(U,\bar U)/(|U||\bar U|)$, where $C(U,\bar U)$ counts only the edges directed from $U$ to $\bar U$.
--
--   This is the directed max-flow min-cut theorem of Leighton and Rao: the directed min-cut approximates the directed uniform concurrent flow within an $O(\log n)$ factor, which underlies their approximation algorithms for directed cut problems such as minimum feedback arc set.
--
--   **Formalization Note** The $\Omega$ is an absolute constant, quantified before the network. The paper's standing connectivity assumption is not imposed: without strong connectivity some proper cut has capacity $0$, so $\mathcal S=0=f$ and the statement holds trivially, hence dropping it only strengthens the theorem. $n\ge2$ is required since no cut exists otherwise.
-- source:
--   Leighton and Rao, Multicommodity max-flow min-cut theorems and their use in designing approximation algorithms, J. ACM 46 (1999), p. 804, Theorem 12 (proof p. 807)

import Mathlib
import Definitions.Def_LeightonRao_Directed_Setting

namespace LeightonRao.Directed

/-- Leighton–Rao, Theorem 12, p. 804. There is an absolute constant `c > 0` such that for every
directed UMFP with `n ≥ 2` nodes, `c · 𝒮 / log₂ n ≤ f ≤ 𝒮`, where `f` is the max-flow and `𝒮` the
directed min-cut. -/
theorem theorem_12 :
    ∃ c : ℝ, 0 < c ∧ ∀ {V : Type} [Fintype V] [DecidableEq V] (N : DiNetwork V),
      2 ≤ Fintype.card V →
      c * diMinCut N / Real.logb 2 (Fintype.card V) ≤ diMaxFlow N diDemand ∧
      diMaxFlow N diDemand ≤ diMinCut N := by sorry

end LeightonRao.Directed
