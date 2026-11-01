-- Prove2me | Theorems.Thm_MVBlossoms_corollary_3
-- name    : MVBlossoms.corollary_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:45:42.745079+00:00
-- url     : https://prove2.me/theorems/05ea0ae2-6251-4fc4-9959-4a532349ee28
-- title:
--   Corollary 3 — the ends of a matched edge of tenacity $t_m$ share their base and blossom
-- statement:
--   Let $(u,v)$ be a matched edge with $\mathrm{tenacity}(u,v)=t_m$. Then $u$ and $v$ have the same base $b$, and both belong to the blossom $B_{b,t_m}$.
--
--   **Formalization Note** Throughout, $G=(V,E)$ is a finite simple graph and $M$ a matching of $G$; levels and tenacities take values in $\mathbb N\cup\{\infty\}$. The section's standing assumption $t_m<l_m$ (p.2018: \"Henceforth, we will assume that $t_m<l_m$\") is a hypothesis.
--
--   Differences from the source:
--   - encoding: levels, tenacities and l_m equal ∞ when no path exists (Definitions 3, 4) → values in ℕ∞, defined as infima (⊤ for an empty family); reason: Lean convention; same instances
--   - encoding: b = base(v), the unique element of B(v) (Definitions 21, 29) → conclusion ∃ b, IsBase M u b ∧ IsBase M v b, where IsBase M x b is baseSet M x = {b}; reason: no junk value for base(·); "have the same base, say b" asserts that both bases exist and coincide
--   - encoding: B_{b,t} by Definitions 22 and 31, union over basal v → one recursion blossom M b t on t, union over all w ∈ T_{b,t} ∪ {b}; reason: a non-basal w has an empty blossom, so the union is unchanged; at t = t_m it is Definition 22
--   - encoding: the blossom B_{b,t_m} → blossom M b t₀ with t₀ : ℕ and (t₀ : ℕ∞) = t_m; reason: t_m is finite under t_m < l_m; t₀ is that natural number
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Corollary 3, p.2031

import Mathlib
import Definitions.Def_MVBlossoms_edgeTenacity
import Definitions.Def_MVBlossoms_lm
import Definitions.Def_MVBlossoms_tm
import Definitions.Def_MVBlossoms_IsBase
import Definitions.Def_MVBlossoms_blossom

namespace MVBlossoms

/-- **Corollary 3.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Corollary 3, p.2031: "Let (u, v) be a matched edge of tenacity
tm. Then, u and v have the same base, say b, and both belong to the same blossom of tenacity tm,
namely B_{b,tm}."

**Formalization Note.** `V` is finite (`Fintype`), `G` is a simple graph and `M` a matching (`hM`); levels and
tenacities are in `ℕ∞` (definitions `evenLevel`, `oddLevel`, `tenacity`, `edgeTenacity`). The paper's standing assumption `t_m < l_m` ("Henceforth, we will assume that tm<lm",
p.2018; restated on p.2027) is the hypothesis `hstd`. `t₀ : ℕ` is `t_m` as a natural number (finite, since
`t_m < l_m`); the blossom is `blossom M b t₀`. -/
theorem corollary_3 {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} (M : G.Subgraph)
    (hM : M.IsMatching) (hstd : tm M < lm M)
    (t₀ : ℕ) (ht₀ : (t₀ : ℕ∞) = tm M)
    (u v : V) (huv : s(u, v) ∈ M.edgeSet) (hten : edgeTenacity M u v = tm M) :
    ∃ b : V, IsBase M u b ∧ IsBase M v b ∧ u ∈ blossom M b t₀ ∧ v ∈ blossom M b t₀ := by sorry

end MVBlossoms
