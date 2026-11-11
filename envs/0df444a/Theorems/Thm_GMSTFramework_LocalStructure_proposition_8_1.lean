-- Prove2me | Theorems.Thm_GMSTFramework_LocalStructure_proposition_8_1
-- name    : GMSTFramework.LocalStructure.proposition_8_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:03:26.949022+00:00
-- url     : https://prove2.me/theorems/0ba56095-36e9-4002-90da-9599bbc78fe1
-- title:
--   Proposition 8.1 — a society of depth at most $k$ has a linear decomposition of adhesion at most $k$ [RS90]
-- statement:
--   (Cited from [RS90] as printed in this paper.) Let $k\ge0$ and let $(G,\Omega)$ be a society of depth at most $k$. Then $(G,\Omega)$ has a linear decomposition of adhesion at most $k$.
--
--   Differences from the source:
--   - encoding: a society (G, Ω), Ω a cyclic ordering of V(Ω) ⊆ V(G) → a duplicate-free list Ω read cyclically, the graph as ⊤ : G.Subgraph; reason: a cyclic ordering is a list up to rotation
--   - encoding: depth at most k (maximum order of a transaction) → DepthLE: every transaction has order ≤ k; reason: the same
--   - encoding: labelling v₁, …, vₙ appearing in Ω in the order listed → Ω read from a starting position (a rotation); reason: the same labellings
-- source:
--   Gorsky, Protopapas, Wiederrecht, A unifying framework for Graph Minor Structure Theorems with polynomial bounds, STOC 2027 submission (manuscript sha256 b2ee466d…), Proposition 8.1, p. 84 (PDF 87)

import Mathlib
import Definitions.Def_GMSTFramework_LocalStructure_Societies

open scoped Classical

namespace GMSTFramework.LocalStructure

/-- Proposition 8.1 ([RS90]): a society of depth at most `k` has a linear decomposition of adhesion
at most `k`. -/
theorem proposition_8_1 :
    ∀ k : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (Ω : List V),
      Ω.Nodup → DepthLE (⊤ : G.Subgraph) Ω k →
        ∃ D : LinearDecomposition (⊤ : G.Subgraph) Ω, D.AdhesionLE k := by sorry

end GMSTFramework.LocalStructure
