-- Prove2me | Theorems.Thm_MultiplierAssoc206_Resolution_theorem_5_4
-- name    : MultiplierAssoc206.Resolution.theorem_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:12:27.047714+00:00
-- url     : https://prove2.me/theorems/e7daebe1-d7e2-4103-92a6-18d443525ca5
-- title:
--   Bounded-degree boundary expanders with a matching covering $V$
-- statement:
--   There are absolute constants $\Delta\in\mathbb N$, $\Gamma\ge1$ and $\varepsilon>0$ and an $m_0$ such that for every $m\ge m_0$ there is a bipartite graph $H=(U,V,E)$ with $|U|=m+1$ and $|V|=m$, of maximum degree at most $\Delta$, that is an $(\varepsilon m,\Gamma)$-boundary expander:
--   $$|\delta(S)|\ge\Gamma\,|S|\qquad\text{for every }S\subseteq U\text{ with }|S|\le\varepsilon m,$$
--   and has a matching covering $V$.
--
--   These graphs, due to Itsykson, Slabodkin and Sokolov, carry the hard perfect-matching instances embedded into $\mathsf{Assoc}_n$.
--
--   Differences from the source:
--   - encoding: a bipartite graph H = (U, V, E) with |U| = m+1, |V| = m, for every sufficiently large m → U = Fin (m+1), V = Fin m, E ⊆ U × V, and an explicit threshold m₀; reason: relabeling the vertices; no parallel edges, as in §2's notation e = (u_e, v_e)
-- source:
--   Vincent Liew, Associativity of Multiplication Is Hard for Resolution, STOC 2027 submission #206 (October 2026), source.pdf SHA-256 676dcc4be9158c52d07aec1c9d48f53fa38289ed1b4dcb34b53adc70dbdd5ead, PDF p.9 (printed p.8), Theorem 5.4 ([ISS15, IOSS16])

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_Graph

namespace MultiplierAssoc206.Resolution

/-- Theorem 5.4 ([ISS15, IOSS16]), PDF p.9 (printed p.8): bounded-degree boundary expanders
with `|U| = m + 1`, `|V| = m` and a matching covering `V`. -/
theorem theorem_5_4 :
    ∃ (Δ : ℕ) (Γ ε : ℝ), 1 ≤ Γ ∧ 0 < ε ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∃ E : Finset (Fin (m + 1) × Fin m),
        MaxDegLE E Δ ∧ IsBoundaryExpander E (ε * m) Γ ∧ HasMatchingCoveringV E := by sorry

end MultiplierAssoc206.Resolution
