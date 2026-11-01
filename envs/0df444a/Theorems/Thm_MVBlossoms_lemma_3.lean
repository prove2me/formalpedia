-- Prove2me | Theorems.Thm_MVBlossoms_lemma_3
-- name    : MVBlossoms.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:45:01.415459+00:00
-- url     : https://prove2.me/theorems/0ae4bb05-f249-42f7-95f0-196c30c84f92
-- title:
--   Lemma 3 (corrected: finite tenacity in clause 2) — tenacity bound at an unmatched bridge
-- statement:
--   Let $(u,v)$ be an unmatched edge of $G$ that is a bridge. Then
--
--   1. $\mathrm{tenacity}(v)\le \mathrm{tenacity}(u,v)$; and
--   2. if $\mathrm{tenacity}(v)=\mathrm{tenacity}(u,v)<\infty$, then $v$ is an outer vertex.
--
--   The lemma is used for bridges of tenacity at most $l_m$, which are finite.
--
--   **Formalization Note** Throughout, $G=(V,E)$ is a finite simple graph and $M$ a matching of $G$; levels and tenacities take values in $\mathbb N\cup\{\infty\}$. The section's standing assumption $t_m<l_m$ (p.2018: \"Henceforth, we will assume that $t_m<l_m$\") is a hypothesis.
--
--   Differences from the source:
--   - correction: clause 2: if tenacity(v) = tenacity(u,v), then v is outer → clause 2 also assumes edgeTenacity M u v ≠ ⊤; reason: false for infinite tenacity: a triangle f,x,y with M ∋ xy (t_m = 3 < l_m = ∞) next to the path a–b–c–d with M ∋ ab, cd; (b,c) is an unmatched bridge with tenacity(c) = tenacity(b,c) = ∞ and c is not outer (no finite min level); proved in Solutions/verification/MVBlossoms_LemmaThreeCounterexample.lean
--   - encoding: levels, tenacities and l_m equal ∞ when no path exists (Definitions 3, 4) → values in ℕ∞, defined as infima (⊤ for an empty family); reason: Lean convention; same instances
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Lemma 3, p.2026

import Mathlib
import Definitions.Def_MVBlossoms_IsOuter
import Definitions.Def_MVBlossoms_tenacity
import Definitions.Def_MVBlossoms_edgeTenacity
import Definitions.Def_MVBlossoms_lm
import Definitions.Def_MVBlossoms_tm
import Definitions.Def_MVBlossoms_IsBridge

namespace MVBlossoms

/-- **Lemma 3 (corrected: finite tenacity in clause 2).** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Lemma 3, p.2026: "Let (u, v)
be an unmatched bridge. Then, 1. tenacity(v) ≤ tenacity(u,v); and 2. if tenacity(v) =
tenacity(u,v), then v is an outer vertex."

**Formalization Note.** `V` is finite (`Fintype`), `G` is a simple graph and `M` a matching (`hM`); levels and
tenacities are in `ℕ∞` (definitions `evenLevel`, `oddLevel`, `tenacity`, `edgeTenacity`). The paper's standing assumption `t_m < l_m` ("Henceforth, we will assume that tm<lm",
p.2018; restated on p.2027) is the hypothesis `hstd`. Clause 2 additionally assumes `tenacity(u,v) < ∞`: as
printed it fails for bridges of infinite tenacity (the path a–b–c–d with M = {ab, cd}, next to a
triangle f, x, y with M ∋ xy so that t_m = 3 < l_m = ∞: the edge (b, c) is an unmatched bridge with
tenacity(c) = tenacity(b, c) = ∞, and c has no finite min level, so it is not outer). -/
theorem lemma_3 {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} (M : G.Subgraph)
    (hM : M.IsMatching) (hstd : tm M < lm M)
    (u v : V) (hadj : G.Adj u v) (hun : s(u, v) ∉ M.edgeSet) (hbr : IsBridge M u v) :
    tenacity M v ≤ edgeTenacity M u v ∧
      (tenacity M v = edgeTenacity M u v → edgeTenacity M u v ≠ ⊤ → IsOuter M v) := by sorry

end MVBlossoms
