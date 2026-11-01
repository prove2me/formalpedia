-- Prove2me | Theorems.Thm_MVBlossoms_lemma_6
-- name    : MVBlossoms.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:45:10.955115+00:00
-- url     : https://prove2.me/theorems/d97b7f63-6aa2-4964-9b07-6abacdde8b78
-- title:
--   Lemma 6 — min level paths to endpoints of bridges of tenacity $t_m$ consist of props
-- statement:
--   Let $T_m$ be the set of endpoints of bridges of tenacity $t_m$. If $v\in T_m$ and $p$ is a min level($v$) path, then every edge of $p$ is a prop.
--
--   **Formalization Note** Throughout, $G=(V,E)$ is a finite simple graph and $M$ a matching of $G$; levels and tenacities take values in $\mathbb N\cup\{\infty\}$. The section's standing assumption $t_m<l_m$ (p.2018: \"Henceforth, we will assume that $t_m<l_m$\") is a hypothesis.
--
--   Differences from the source:
--   - encoding: levels, tenacities and l_m equal ∞ when no path exists (Definitions 3, 4) → values in ℕ∞, defined as infima (⊤ for an empty family); reason: Lean convention; same instances
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Lemma 6, p.2029

import Mathlib
import Definitions.Def_MVBlossoms_IsMinLevelPath
import Definitions.Def_MVBlossoms_edgeTenacity
import Definitions.Def_MVBlossoms_lm
import Definitions.Def_MVBlossoms_tm
import Definitions.Def_MVBlossoms_IsProp
import Definitions.Def_MVBlossoms_IsBridge

namespace MVBlossoms

/-- **Lemma 6.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Lemma 6, p.2029: "Let v ∈ Tm, and let p be a min level(v) path.
Then, all edges on p are props." Here "Bm denote[s] the set of all bridges of tenacity tm ... and
let Tm denote the set of endpoints of bridges in Bm" (p.2029).

**Formalization Note.** `V` is finite (`Fintype`), `G` is a simple graph and `M` a matching (`hM`); levels and
tenacities are in `ℕ∞` (definitions `evenLevel`, `oddLevel`, `tenacity`, `edgeTenacity`). The paper's standing assumption `t_m < l_m` ("Henceforth, we will assume that tm<lm",
p.2018; restated on p.2027) is the hypothesis `hstd`. `v ∈ T_m` is: `v` is an endpoint of a bridge `(v, w)` of
tenacity `t_m` (bridges are symmetric). -/
theorem lemma_6 {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} (M : G.Subgraph)
    (hM : M.IsMatching) (hstd : tm M < lm M)
    (v w : V) (hbr : IsBridge M v w) (hten : edgeTenacity M v w = tm M)
    {f : V} (p : G.Walk f v) (hp : IsMinLevelPath M p) :
    ∀ a b : V, s(a, b) ∈ p.edges → IsProp M a b := by sorry

end MVBlossoms
