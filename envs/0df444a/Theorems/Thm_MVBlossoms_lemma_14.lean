-- Prove2me | Theorems.Thm_MVBlossoms_lemma_14
-- name    : MVBlossoms.lemma_14
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:43:15.048141+00:00
-- url     : https://prove2.me/theorems/7cb23007-27d7-47ad-b2c9-33f58b3ea37d
-- title:
--   Lemma 14 — on a shortest even path, a vertex of tenacity $t_m$ is BFS honest with respect to its base
-- statement:
--   Let $p$ be an even level($v$) path from an unmatched vertex $f$ to a vertex $v$. Let $w$ lie on $p$ with $\mathrm{tenacity}(w)=t_m$ and let $b=\mathrm{base}(w)$. Then $b$ lies on $p$, and $p[b\text{ to }w]$ is an even level($b;w$) path if its length is even and an odd level($b;w$) path if its length is odd.
--
--   This is Statement 5 of Theorem 3 at $t=t_m$.
--
--   **Formalization Note** Throughout, $G=(V,E)$ is a finite simple graph and $M$ a matching of $G$; levels and tenacities take values in $\mathbb N\cup\{\infty\}$. The section's standing assumption $t_m<l_m$ (p.2018: \"Henceforth, we will assume that $t_m<l_m$\") is a hypothesis.
--
--   Differences from the source:
--   - encoding: levels, tenacities and l_m equal ∞ when no path exists (Definitions 3, 4) → values in ℕ∞, defined as infima (⊤ for an empty family); reason: Lean convention; same instances
--   - encoding: b = base(v), the unique element of B(v) (Definitions 21, 29) → hypothesis IsBase M v b, i.e. baseSet M v = {b}, for every such b; reason: no junk value for base(v); together with Statement 2 / Corollary 2 it is the printed claim
--   - encoding: p[b to u], b before or after u on p (Definitions 7, 24, 33) → some q : G.Walk b u with IsSegmentFrom p q (p = p₁ q p₂ or p = p₁ q⁻¹ p₂); reason: on a simple path the segment exists and is unique when b, u lie on p
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Lemma 14, p.2032

import Mathlib
import Definitions.Def_MVBlossoms_IsEvenLevelPath
import Definitions.Def_MVBlossoms_tenacity
import Definitions.Def_MVBlossoms_lm
import Definitions.Def_MVBlossoms_tm
import Definitions.Def_MVBlossoms_IsBase
import Definitions.Def_MVBlossoms_IsBFSHonestWrt

namespace MVBlossoms

/-- **Lemma 14.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Lemma 14, p.2032: "Let p be an even level(v) path from unmatched
vertex f to an arbitrary vertex v. Let w ∈ p with tenacity(w) = tm, and let b = base(w). Then, b also
lies on p, and w is BFS honest on p w.r.t. b."

**Formalization Note.** `V` is finite (`Fintype`), `G` is a simple graph and `M` a matching (`hM`); levels and
tenacities are in `ℕ∞` (definitions `evenLevel`, `oddLevel`, `tenacity`, `edgeTenacity`). The paper's standing assumption `t_m < l_m` ("Henceforth, we will assume that tm<lm",
p.2018; restated on p.2027) is the hypothesis `hstd`. BFS honesty w.r.t. `b` is `IsBFSHonestWrt` (Definition
24). -/
theorem lemma_14 {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} (M : G.Subgraph)
    (hM : M.IsMatching) (hstd : tm M < lm M)
    {f v : V} (p : G.Walk f v) (hp : IsEvenLevelPath M p)
    (w : V) (hw : w ∈ p.support) (hten : tenacity M w = tm M) (b : V) (hb : IsBase M w b) :
    b ∈ p.support ∧ IsBFSHonestWrt M p w b := by sorry

end MVBlossoms
