-- Prove2me | Theorems.Thm_MVBlossoms_theorem_2
-- name    : MVBlossoms.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:41:16.360405+00:00
-- url     : https://prove2.me/theorems/7ba716ca-a69e-4bcc-91db-ab492144752b
-- title:
--   Theorem 2 — vertices of at least the end's tenacity are BFS honest
-- statement:
--   Let $p$ be an even level($v$) or odd level($v$) path starting at an unmatched vertex $f$, and let $u$ be a vertex of $p$ with $\mathrm{tenacity}(u)\ge\mathrm{tenacity}(v)$. Then $u$ is BFS honest on $p$: the part $p[f\text{ to }u]$ of $p$ is a shortest alternating path to $u$ of its parity. Moreover, if $\mathrm{tenacity}(u)>\mathrm{tenacity}(v)$, then
--
--   $$
--   |p[f\text{ to }u]|=\mathrm{min\ level}(u).
--   $$
--
--   This "limited BFS honesty" is the substitute, in general graphs, for the BFS honesty of every vertex that holds in bipartite graphs.
--
--   **Formalization Note** Throughout, $G=(V,E)$ is a finite simple graph and $M$ a matching of $G$; levels and tenacities take values in $\mathbb N\cup\{\infty\}$. The section's standing assumption $t_m<l_m$ (p.2018: \"Henceforth, we will assume that $t_m<l_m$\") is a hypothesis.
--
--   Differences from the source:
--   - encoding: levels, tenacities and l_m equal ∞ when no path exists (Definitions 3, 4) → values in ℕ∞, defined as infima (⊤ for an empty family); reason: Lean convention; same instances
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Theorem 2, p.2027

import Mathlib
import Definitions.Def_MVBlossoms_IsEvenLevelPath
import Definitions.Def_MVBlossoms_IsOddLevelPath
import Definitions.Def_MVBlossoms_minLevel
import Definitions.Def_MVBlossoms_tenacity
import Definitions.Def_MVBlossoms_lm
import Definitions.Def_MVBlossoms_tm
import Definitions.Def_MVBlossoms_IsBFSHonest

namespace MVBlossoms

/-- **Theorem 2.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Theorem 2, p.2027: "Let p be an even level(v) or odd level(v) path
starting at unmatched vertex f, and let vertex u ∈ p with tenacity(u) ≥ tenacity(v). Then, u is
BFS honest on p. Furthermore, if tenacity(u) > tenacity(v), then |p[f to u]| = min level(u)."

**Formalization Note.** `V` is finite (`Fintype`), `G` is a simple graph and `M` a matching (`hM`); levels and
tenacities are in `ℕ∞` (definitions `evenLevel`, `oddLevel`, `tenacity`, `edgeTenacity`). The paper's standing assumption `t_m < l_m` ("Henceforth, we will assume that tm<lm",
p.2018; restated on p.2027) is the hypothesis `hstd`. `|p[f to u]|` is `(p.takeUntil u hu).length`. -/
theorem theorem_2 {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} (M : G.Subgraph)
    (hM : M.IsMatching) (hstd : tm M < lm M)
    {f v : V} (p : G.Walk f v) (hp : IsEvenLevelPath M p ∨ IsOddLevelPath M p)
    (u : V) (hu : u ∈ p.support) (hten : tenacity M v ≤ tenacity M u) :
    IsBFSHonest M p u hu ∧
      (tenacity M v < tenacity M u → ((p.takeUntil u hu).length : ℕ∞) = minLevel M u) := by sorry

end MVBlossoms
