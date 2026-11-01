-- Prove2me | Theorems.Thm_MVBlossoms_corollary_4
-- name    : MVBlossoms.corollary_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:45:36.989757+00:00
-- url     : https://prove2.me/theorems/6580d31f-2e54-4a6e-9563-667fb12f16a0
-- title:
--   Corollary 4 — structure of shortest paths to a vertex of tenacity $t_m$
-- statement:
--   Let $v\in U_m$ and $b=\mathrm{base}(v)$. Then:
--
--   1. $v$ has a matched neighbour, and every matched neighbour of $v$ lies in the blossom $B_{b,t_m}$;
--   2. every even level($v$) path is an even level($b$) path followed by an even level($b;v$) path, and every odd level($v$) path is an even level($b$) path followed by an odd level($b;v$) path; in both cases the second part lies in $B_{b,t_m}\cup\{b\}$.
--
--   This is Statement 3 of Theorem 3 at $t=t_m$.
--
--   **Formalization Note** Throughout, $G=(V,E)$ is a finite simple graph and $M$ a matching of $G$; levels and tenacities take values in $\mathbb N\cup\{\infty\}$. The section's standing assumption $t_m<l_m$ (p.2018: \"Henceforth, we will assume that $t_m<l_m$\") is a hypothesis.
--
--   Differences from the source:
--   - encoding: levels, tenacities and l_m equal ∞ when no path exists (Definitions 3, 4) → values in ℕ∞, defined as infima (⊤ for an empty family); reason: Lean convention; same instances
--   - encoding: b = base(v), the unique element of B(v) (Definitions 21, 29) → hypothesis IsBase M v b, i.e. baseSet M v = {b}, for every such b; reason: no junk value for base(v); together with Statement 2 / Corollary 2 it is the printed claim
--   - encoding: B_{b,t} by Definitions 22 and 31, union over basal v → one recursion blossom M b t on t, union over all w ∈ T_{b,t} ∪ {b}; reason: a non-basal w has an empty blossom, so the union is unchanged; at t = t_m it is Definition 22
--   - encoding: the blossom B_{b,t_m} → blossom M b t₀ with t₀ : ℕ and (t₀ : ℕ∞) = t_m; reason: t_m is finite under t_m < l_m; t₀ is that natural number
--   - encoding: "the matched neighbor of v also lies in the blossom" → some matched neighbour exists, and every v' with s(v,v') ∈ M lies in the blossom; reason: the definite description presupposes a matched neighbour (v ∈ U_m is matched since unmatched vertices have tenacity ≥ l_m > t_m), which is unique because M is a matching
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Corollary 4, p.2031

import Mathlib
import Definitions.Def_MVBlossoms_IsEvenLevelPath
import Definitions.Def_MVBlossoms_IsOddLevelPath
import Definitions.Def_MVBlossoms_tenacity
import Definitions.Def_MVBlossoms_lm
import Definitions.Def_MVBlossoms_tm
import Definitions.Def_MVBlossoms_IsBase
import Definitions.Def_MVBlossoms_IsEvenLevelFromPath
import Definitions.Def_MVBlossoms_IsOddLevelFromPath
import Definitions.Def_MVBlossoms_blossom

namespace MVBlossoms

/-- **Corollary 4.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Corollary 4, p.2031: "Let v ∈ Um and b = base(v). Then, the
matched neighbor of v also lies in the blossom, and every even level(v) (odd level(v)) path consists
of an even level(b) path followed by an even level(b;v) (odd level(b;v)) path, where the latter lies
in B_{b,tm} ∪ {b}."

**Formalization Note.** `V` is finite (`Fintype`), `G` is a simple graph and `M` a matching (`hM`); levels and
tenacities are in `ℕ∞` (definitions `evenLevel`, `oddLevel`, `tenacity`, `edgeTenacity`). The paper's standing assumption `t_m < l_m` ("Henceforth, we will assume that tm<lm",
p.2018; restated on p.2027) is the hypothesis `hstd`. `t₀ : ℕ` is `t_m`. The conclusion also records that `v`
has a matched neighbor (the article's "the matched neighbor of v" presupposes it). -/
theorem corollary_4 {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} (M : G.Subgraph)
    (hM : M.IsMatching) (hstd : tm M < lm M)
    (t₀ : ℕ) (ht₀ : (t₀ : ℕ∞) = tm M) (v b : V) (hv : tenacity M v = tm M) (hb : IsBase M v b) :
    ((∃ v' : V, s(v, v') ∈ M.edgeSet) ∧ ∀ v' : V, s(v, v') ∈ M.edgeSet → v' ∈ blossom M b t₀) ∧
    ∀ (f : V) (p : G.Walk f v),
      (IsEvenLevelPath M p → ∃ (p₁ : G.Walk f b) (q : G.Walk b v), p = p₁.append q ∧
        IsEvenLevelPath M p₁ ∧ IsEvenLevelFromPath M q ∧
        ∀ x ∈ q.support, x ∈ blossom M b t₀ ∨ x = b) ∧
      (IsOddLevelPath M p → ∃ (p₁ : G.Walk f b) (q : G.Walk b v), p = p₁.append q ∧
        IsEvenLevelPath M p₁ ∧ IsOddLevelFromPath M q ∧
        ∀ x ∈ q.support, x ∈ blossom M b t₀ ∨ x = b) := by sorry

end MVBlossoms
