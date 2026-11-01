-- Prove2me | Theorems.Thm_MVBlossoms_corollary_2
-- name    : MVBlossoms.corollary_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:42:07.543835+00:00
-- url     : https://prove2.me/theorems/cb02d00b-6265-4ca4-875a-63d3c3cde53e
-- title:
--   Corollary 2 — $B(v)$ is a singleton for every vertex of tenacity $t_m$
-- statement:
--   Let $U_m=\{v\in V:\mathrm{tenacity}(v)=t_m\}$. For every $v\in U_m$ the set
--
--   $$
--   B(v)=\{F(p,v): p\text{ an even level}(v)\text{ or odd level}(v)\text{ path}\}
--   $$
--
--   has exactly one element. This is Statement 2 of Theorem 3 at $t=t_m$; it makes $\mathrm{base}(v)$ well defined.
--
--   **Formalization Note** Throughout, $G=(V,E)$ is a finite simple graph and $M$ a matching of $G$; levels and tenacities take values in $\mathbb N\cup\{\infty\}$. The section's standing assumption $t_m<l_m$ (p.2018: \"Henceforth, we will assume that $t_m<l_m$\") is a hypothesis.
--
--   Differences from the source:
--   - encoding: levels, tenacities and l_m equal ∞ when no path exists (Definitions 3, 4) → values in ℕ∞, defined as infima (⊤ for an empty family); reason: Lean convention; same instances
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Corollary 2, p.2030

import Mathlib
import Definitions.Def_MVBlossoms_tenacity
import Definitions.Def_MVBlossoms_lm
import Definitions.Def_MVBlossoms_tm
import Definitions.Def_MVBlossoms_baseSet

namespace MVBlossoms

/-- **Corollary 2.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Corollary 2, p.2030: "For every v ∈ Um, the set B(v) is a
singleton." Here Um = {v ∈ V | tenacity(v) = tm} (p.2029).

**Formalization Note.** `V` is finite (`Fintype`), `G` is a simple graph and `M` a matching (`hM`); levels and
tenacities are in `ℕ∞` (definitions `evenLevel`, `oddLevel`, `tenacity`, `edgeTenacity`). The paper's standing assumption `t_m < l_m` ("Henceforth, we will assume that tm<lm",
p.2018; restated on p.2027) is the hypothesis `hstd`. -/
theorem corollary_2 {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} (M : G.Subgraph)
    (hM : M.IsMatching) (hstd : tm M < lm M) :
    ∀ v : V, tenacity M v = tm M → ∃ b : V, baseSet M v = {b} := by sorry

end MVBlossoms
