-- Prove2me | Theorems.Thm_LeightonRao_Directed_weak_duality
-- name    : LeightonRao.Directed.weak_duality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:23:12.229345+00:00
-- url     : https://prove2.me/theorems/4c467400-c1f5-4d02-a5d2-0edda81f903a
-- title:
--   p. 804 — directed weak duality: a concurrent flow of value λ satisfies λ|U||Ū| ≤ C(U, Ū)
-- statement:
--   Let $G$ be a directed network on $V$ and let $f$ be a concurrent flow of value $\lambda$ for the directed uniform multicommodity flow problem (demand $1$ from $u$ to $v$ for every ordered pair $u\ne v$). Then for every nonempty proper subset $U\subsetneq V$,
--   $$\lambda\,|U|\,|\bar U|\le C(U,\bar U),$$
--   where $C(U,\bar U)$ is the total capacity of the edges directed from $U$ to $\bar U$.
--
--   Taking the supremum over flows and the minimum over cuts gives the upper bound $f\le\mathcal S$ of Theorem 12, which the paper says "follows immediately from the definitions".
--
--   **Formalization Note** Each of the $|U|\,|\bar U|$ commodities $(u,v)$ with $u\in U$, $v\notin U$ must cross the cut in the forward direction. No connectivity assumption is needed.
-- source:
--   Leighton and Rao, Multicommodity max-flow min-cut theorems and their use in designing approximation algorithms, J. ACM 46 (1999), p. 804, §2.4, sentence after Theorem 12 (f ≤ 𝒮)

import Mathlib
import Definitions.Def_LeightonRao_Directed_Setting

namespace LeightonRao.Directed

/-- Leighton–Rao, p. 804: "The fact that f ≤ 𝒮 follows immediately from the definitions." For every
directed concurrent flow of value `lam` for the directed UMFP and every nonempty proper `U`,
`lam · |U| |Ū| ≤ C(U, Ū)`. -/
theorem weak_duality {V : Type} [Fintype V] [DecidableEq V] (N : DiNetwork V)
    (f : V → V → V → V → ℝ) (lam : ℝ) (hf : IsDiConcurrentFlow N diDemand f lam)
    (U : Finset V) (hU : U.Nonempty) (hUc : Uᶜ.Nonempty) :
    lam * ((U.card : ℝ) * (Uᶜ.card : ℝ)) ≤ diCutCap N U := by sorry

end LeightonRao.Directed
