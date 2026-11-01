-- Prove2me | Theorems.Thm_MVBlossoms_lemma_5
-- name    : MVBlossoms.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:45:07.388579+00:00
-- url     : https://prove2.me/theorems/ff101886-5705-479b-b6f0-744b9cfe1ea2
-- title:
--   Lemma 5 — a max level path to a vertex of tenacity $t_m$ contains a unique bridge of tenacity $t_m$
-- statement:
--   Let $v$ be a vertex with $\mathrm{tenacity}(v)=t_m$ and let $p$ be a max level($v$) path. Then exactly one edge of $p$ is a bridge of tenacity $t_m$.
--
--   This is Statement 1 of Theorem 3 at $t=t_m$, with uniqueness.
--
--   **Formalization Note** Throughout, $G=(V,E)$ is a finite simple graph and $M$ a matching of $G$; levels and tenacities take values in $\mathbb N\cup\{\infty\}$. The section's standing assumption $t_m<l_m$ (p.2018: \"Henceforth, we will assume that $t_m<l_m$\") is a hypothesis.
--
--   Differences from the source:
--   - encoding: levels, tenacities and l_m equal ∞ when no path exists (Definitions 3, 4) → values in ℕ∞, defined as infima (⊤ for an empty family); reason: Lean convention; same instances
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Lemma 5, p.2028

import Mathlib
import Definitions.Def_MVBlossoms_IsMaxLevelPath
import Definitions.Def_MVBlossoms_tenacity
import Definitions.Def_MVBlossoms_edgeTenacity
import Definitions.Def_MVBlossoms_lm
import Definitions.Def_MVBlossoms_tm
import Definitions.Def_MVBlossoms_IsBridge

namespace MVBlossoms

/-- **Lemma 5.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Lemma 5, p.2028: "Let v be a vertex of tenacity tm and p be a max
level(v) path. Then, p contains a unique bridge of tenacity tm."

**Formalization Note.** `V` is finite (`Fintype`), `G` is a simple graph and `M` a matching (`hM`); levels and
tenacities are in `ℕ∞` (definitions `evenLevel`, `oddLevel`, `tenacity`, `edgeTenacity`). The paper's standing assumption `t_m < l_m` ("Henceforth, we will assume that tm<lm",
p.2018; restated on p.2027) is the hypothesis `hstd`. Edges of `p` are unordered pairs `e : Sym2 V`
(`p.edges`); uniqueness is `∃!` over them. -/
theorem lemma_5 {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} (M : G.Subgraph)
    (hM : M.IsMatching) (hstd : tm M < lm M)
    (v : V) (hv : tenacity M v = tm M) {f : V} (p : G.Walk f v) (hp : IsMaxLevelPath M p) :
    ∃! e : Sym2 V, e ∈ p.edges ∧
      ∃ a b : V, e = s(a, b) ∧ IsBridge M a b ∧ edgeTenacity M a b = tm M := by sorry

end MVBlossoms
