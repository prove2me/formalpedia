-- Prove2me | Theorems.Thm_MurtySimon_IsEdgeMatching_eq_of_mem
-- name    : MurtySimon.IsEdgeMatching.eq_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:58:39.547821+00:00
-- url     : https://prove2.me/theorems/d22cecd7-d1af-45b0-b84d-8a76f68bf20d
-- title:
--   Is Edge Matching: eq of mem
-- statement:
--   The Is Edge Matching construction uses the eq of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Bound.lean#L48-L52
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Bound.lean#L48-L52

module
public import Definitions.Def_MurtySimon_Components
public import Definitions.Def_MurtySimon_Bound
set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
noncomputable section
variable {M : Finset (Sym2 V)}

theorem MurtySimon.IsEdgeMatching.eq_of_mem (hM : IsEdgeMatching G M) {x y z : V} (h1 : s(x, y) ∈ M)
    (h2 : s(x, z) ∈ M) : y = z := by sorry
