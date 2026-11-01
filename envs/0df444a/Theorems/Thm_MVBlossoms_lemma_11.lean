-- Prove2me | Theorems.Thm_MVBlossoms_lemma_11
-- name    : MVBlossoms.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:43:19.546796+00:00
-- url     : https://prove2.me/theorems/a3969a00-895a-43f2-a7e5-30bf08bc4412
-- title:
--   Lemma 11 — a shortest base-to-vertex path meets a shortest path to the base only at the base
-- statement:
--   Let $v\in U_m$ and $b=\mathrm{base}(v)$. Let $p$ be an even level($b$) path and $q$ an even level($b;v$) or odd level($b;v$) path. Then $b$ is the only vertex common to $p$ and $q$.
--
--   **Formalization Note** Throughout, $G=(V,E)$ is a finite simple graph and $M$ a matching of $G$; levels and tenacities take values in $\mathbb N\cup\{\infty\}$. The section's standing assumption $t_m<l_m$ (p.2018: \"Henceforth, we will assume that $t_m<l_m$\") is a hypothesis.
--
--   Differences from the source:
--   - encoding: levels, tenacities and l_m equal ∞ when no path exists (Definitions 3, 4) → values in ℕ∞, defined as infima (⊤ for an empty family); reason: Lean convention; same instances
--   - encoding: b = base(v), the unique element of B(v) (Definitions 21, 29) → hypothesis IsBase M v b, i.e. baseSet M v = {b}, for every such b; reason: no junk value for base(v); together with Statement 2 / Corollary 2 it is the printed claim
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Lemma 11, p.2031

import Mathlib
import Definitions.Def_MVBlossoms_IsEvenLevelPath
import Definitions.Def_MVBlossoms_tenacity
import Definitions.Def_MVBlossoms_lm
import Definitions.Def_MVBlossoms_tm
import Definitions.Def_MVBlossoms_IsBase
import Definitions.Def_MVBlossoms_IsEvenLevelFromPath
import Definitions.Def_MVBlossoms_IsOddLevelFromPath

namespace MVBlossoms

/-- **Lemma 11.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Lemma 11, p.2031: "Let v ∈ Um and b = base(v). Let p be an even
level(b) path and q be an even level(b;v) or odd level(b;v) path. Then, q meets p at b only."

**Formalization Note.** `V` is finite (`Fintype`), `G` is a simple graph and `M` a matching (`hM`); levels and
tenacities are in `ℕ∞` (definitions `evenLevel`, `oddLevel`, `tenacity`, `edgeTenacity`). The paper's standing assumption `t_m < l_m` ("Henceforth, we will assume that tm<lm",
p.2018; restated on p.2027) is the hypothesis `hstd`. "b = base(v)" is the hypothesis `IsBase M v b`
(`B(v) = {b}`). -/
theorem lemma_11 {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} (M : G.Subgraph)
    (hM : M.IsMatching) (hstd : tm M < lm M)
    (v b : V) (hv : tenacity M v = tm M) (hb : IsBase M v b)
    {f : V} (p : G.Walk f b) (hp : IsEvenLevelPath M p)
    (q : G.Walk b v) (hq : IsEvenLevelFromPath M q ∨ IsOddLevelFromPath M q) :
    ∀ x : V, x ∈ p.support → x ∈ q.support → x = b := by sorry

end MVBlossoms
