-- Prove2me | Theorems.Thm_MVBlossoms_lemma_1
-- name    : MVBlossoms.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:44:27.968696+00:00
-- url     : https://prove2.me/theorems/9e2d70dd-f08e-4d9c-a72f-1be272e5b0c9
-- title:
--   Lemma 1 — a matched edge of finite tenacity: levels, tenacity, and when it is a bridge
-- statement:
--   Let $(u,v)$ be a matched edge whose tenacity $\mathrm{tenacity}(u,v)=\mathrm{odd\ level}(u)+\mathrm{odd\ level}(v)+1$ is finite. Then
--
--   $$
--   \mathrm{even\ level}(v)=\mathrm{odd\ level}(u)+1,\qquad \mathrm{tenacity}(v)=\mathrm{tenacity}(u,v),
--   $$
--
--   and, writing $\mathrm{tenacity}(u,v)=2i+1$, the edge $(u,v)$ is a bridge if and only if $\mathrm{odd\ level}(u)=\mathrm{odd\ level}(v)=i$.
--
--   By symmetry the same holds with $u$ and $v$ exchanged, so the two levels of one endpoint of a matched edge determine those of the other.
--
--   **Formalization Note** Throughout, $G=(V,E)$ is a finite simple graph and $M$ a matching of $G$; levels and tenacities take values in $\mathbb N\cup\{\infty\}$. The section's standing assumption $t_m<l_m$ (p.2018: \"Henceforth, we will assume that $t_m<l_m$\") is a hypothesis.
--
--   Differences from the source:
--   - encoding: levels, tenacities and l_m equal ∞ when no path exists (Definitions 3, 4) → values in ℕ∞, defined as infima (⊤ for an empty family); reason: Lean convention; same instances
--   - encoding: "where tenacity(u,v) = 2i + 1" → for every natural i with edgeTenacity M u v = 2i + 1; reason: such i exists (a finite edge tenacity is odd) and is unique
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Lemma 1, p.2025

import Mathlib
import Definitions.Def_MVBlossoms_evenLevel
import Definitions.Def_MVBlossoms_oddLevel
import Definitions.Def_MVBlossoms_tenacity
import Definitions.Def_MVBlossoms_edgeTenacity
import Definitions.Def_MVBlossoms_lm
import Definitions.Def_MVBlossoms_tm
import Definitions.Def_MVBlossoms_IsBridge

namespace MVBlossoms

/-- **Lemma 1.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Lemma 1, p.2025: "Let (u, v) be a matched edge of finite tenacity.
Then, even level(v) = odd level(u) + 1 and tenacity(v) = tenacity(u,v). Furthermore, (u, v) is a
bridge if and only if odd level(u) = odd level(v) = i, where tenacity(u,v) = 2i + 1."

**Formalization Note.** `V` is finite (`Fintype`), `G` is a simple graph and `M` a matching (`hM`); levels and
tenacities are in `ℕ∞` (definitions `evenLevel`, `oddLevel`, `tenacity`, `edgeTenacity`). The paper's standing assumption `t_m < l_m` ("Henceforth, we will assume that tm<lm",
p.2018; restated on p.2027) is the hypothesis `hstd`. "i" is any natural number with `tenacity(u,v) = 2i + 1`. -/
theorem lemma_1 {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} (M : G.Subgraph)
    (hM : M.IsMatching) (hstd : tm M < lm M)
    (u v : V) (huv : s(u, v) ∈ M.edgeSet) (hfin : edgeTenacity M u v ≠ ⊤) :
    evenLevel M v = oddLevel M u + 1 ∧ tenacity M v = edgeTenacity M u v ∧
      ∀ i : ℕ, edgeTenacity M u v = ((2 * i + 1 : ℕ) : ℕ∞) →
        (IsBridge M u v ↔ oddLevel M u = (i : ℕ∞) ∧ oddLevel M v = (i : ℕ∞)) := by sorry

end MVBlossoms
