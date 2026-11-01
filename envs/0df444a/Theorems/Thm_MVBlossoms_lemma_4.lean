-- Prove2me | Theorems.Thm_MVBlossoms_lemma_4
-- name    : MVBlossoms.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:44:45.570321+00:00
-- url     : https://prove2.me/theorems/0f87ef74-5411-4392-a683-c7034f5d40ca
-- title:
--   Lemma 4 — an edge of tenacity $t_m$ is a bridge iff both min levels equal $(t_m-1)/2$
-- statement:
--   Let $(u,v)$ be an edge of $G$ with $\mathrm{tenacity}(u,v)=t_m$, and write $t_m=2i+1$. Then $(u,v)$ is a bridge if and only if
--
--   $$
--   \mathrm{min\ level}(u)=\mathrm{min\ level}(v)=i .
--   $$
--
--   **Formalization Note** Throughout, $G=(V,E)$ is a finite simple graph and $M$ a matching of $G$; levels and tenacities take values in $\mathbb N\cup\{\infty\}$. The section's standing assumption $t_m<l_m$ (p.2018: \"Henceforth, we will assume that $t_m<l_m$\") is a hypothesis.
--
--   Differences from the source:
--   - encoding: levels, tenacities and l_m equal ∞ when no path exists (Definitions 3, 4) → values in ℕ∞, defined as infima (⊤ for an empty family); reason: Lean convention; same instances
--   - encoding: "where tm = 2i + 1" → for every natural i with t_m = 2i + 1; reason: such i exists (t_m is finite and odd under t_m < l_m) and is unique
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Lemma 4, p.2028

import Mathlib
import Definitions.Def_MVBlossoms_minLevel
import Definitions.Def_MVBlossoms_edgeTenacity
import Definitions.Def_MVBlossoms_lm
import Definitions.Def_MVBlossoms_tm
import Definitions.Def_MVBlossoms_IsBridge

namespace MVBlossoms

/-- **Lemma 4.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Lemma 4, p.2028: "Let (u, v) be an edge of tenacity tm. Then, (u, v)
is a bridge if and only if min level(u) = min level(v) = i, where tm = 2i + 1."

**Formalization Note.** `V` is finite (`Fintype`), `G` is a simple graph and `M` a matching (`hM`); levels and
tenacities are in `ℕ∞` (definitions `evenLevel`, `oddLevel`, `tenacity`, `edgeTenacity`). The paper's standing assumption `t_m < l_m` ("Henceforth, we will assume that tm<lm",
p.2018; restated on p.2027) is the hypothesis `hstd`. "i" is any natural number with `t_m = 2i + 1`. -/
theorem lemma_4 {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} (M : G.Subgraph)
    (hM : M.IsMatching) (hstd : tm M < lm M)
    (u v : V) (hadj : G.Adj u v) (hten : edgeTenacity M u v = tm M) :
    ∀ i : ℕ, tm M = ((2 * i + 1 : ℕ) : ℕ∞) →
      (IsBridge M u v ↔ minLevel M u = (i : ℕ∞) ∧ minLevel M v = (i : ℕ∞)) := by sorry

end MVBlossoms
