-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_strongPower_isClique_piFinset
-- name    : GroupTheoreticShannonCapacity.strongPower_isClique_piFinset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:25:56.011352+00:00
-- url     : https://prove2.me/theorems/ee012db1-8d6a-4b83-92b5-c214998603db
-- title:
--   Group Theoretic Shannon Capacity: strong Power is Clique pi Finset
-- statement:
--   Product of cliques is a clique in the strong power.
--       If each `sets i` is a clique in G, then their product is a clique in G^⊠n.
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Basic.lean#L96-L113
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Basic.lean#L96-L113

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique
import Definitions.Def_GroupTheoreticShannonCapacity_Defs
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
set_option autoImplicit true
open GroupTheoreticShannonCapacity

theorem GroupTheoreticShannonCapacity.strongPower_isClique_piFinset (G : SimpleGraph V) (n : ℕ)
    (sets : Fin n → Finset V) (hclique : ∀ i, G.IsClique (sets i)) :
    (strongPower G n).IsClique (Fintype.piFinset sets) := by sorry
