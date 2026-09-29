-- Prove2me | Theorems.Thm_OPG434_odd_cycle_equivalence
-- name    : OPG434.odd_cycle_equivalence
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-08T05:04:34.02907+00:00
-- url     : https://prove2.me/theorems/2fe7fa2c-a796-4bee-8d98-3312de07a6b1
-- title:
--   Five bipartite complements iff every color meets every odd cycle
-- statement:
--   For any finite simple graph and any fixed symmetric five-edge labeling, the following are equivalent:
--
--   $$
--   \forall i,\ G-c^{-1}(i)\text{ is bipartite}
--   \quad\Longleftrightarrow\quad
--   \forall i,\ c^{-1}(i)\text{ meets every simple odd cycle of }G.
--   $$
--
--   The cycles need not be induced, and edge deletion retains all vertices. The equivalence does not require triangle-freeness, cubicity, properness, or use of every color.
-- source:
--   VibeMathing candidate_only derivation at commit bc0d53de15bb21236483b4d671dda376309c8177, research/artifacts/candidates/five-transversals-equivalence.md; terminology: Kolman--Lidicky--Sereni, https://kam.mff.cuni.cz/kamserie/clanky/2010/s956.pdf

import Definitions.Def_opg434_weak_pentagon

namespace OPG434

universe u

/-- Deleting every edge of one color is bipartite exactly when that color
meets every simple odd cycle. -/
theorem odd_cycle_equivalence
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (c : EdgeColoring G (Fin 5)) :
    IsWeakPentagonColoring c ↔
      ∀ i : Fin 5, ColorMeetsEveryOddCycle c i := by sorry

end OPG434
