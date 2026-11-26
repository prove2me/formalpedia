-- Prove2me | Theorems.Thm_MurtySimon_mem_Lt
-- name    : MurtySimon.mem_Lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:52:57.377918+00:00
-- url     : https://prove2.me/theorems/d56bf975-dd45-57ea-b84b-cd5c5d6df465
-- title:
--   Murty Simon: mem Lt
-- statement:
--   The Murty Simon construction uses the mem Lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Components.lean#L51-L52
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Components.lean#L51-L52

module
public import Definitions.Def_MurtySimon_Basic
public import Definitions.Def_MurtySimon_Components
set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
noncomputable section

theorem MurtySimon.mem_Lt {M : Finset (Sym2 V)} {e : Sym2 V} : e ∈ Lt G M ↔ e ∈ G.edgeSet ∧ e ∉ M := by sorry
