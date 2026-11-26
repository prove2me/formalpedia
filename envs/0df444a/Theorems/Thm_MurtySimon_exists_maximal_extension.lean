-- Prove2me | Theorems.Thm_MurtySimon_exists_maximal_extension
-- name    : MurtySimon.exists_maximal_extension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:01:31.301406+00:00
-- url     : https://prove2.me/theorems/7d9e584f-b0d7-4fbc-87ae-dbcd00bfd754
-- title:
--   Murty Simon: exists maximal extension
-- statement:
--   The Murty Simon construction uses the exists maximal extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Equality.lean#L38-L47
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Equality.lean#L38-L47

module
public import Definitions.Def_MurtySimon_Bound
public import Definitions.Def_MurtySimon_Equality
set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
noncomputable section

theorem MurtySimon.exists_maximal_extension {N : Finset (Sym2 V)} (hN : IsEdgeMatching G N) :
    ∃ M, N ⊆ M ∧ IsMaximalEdgeMatching G M := by sorry
