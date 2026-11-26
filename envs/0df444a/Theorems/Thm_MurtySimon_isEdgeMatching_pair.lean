-- Prove2me | Theorems.Thm_MurtySimon_isEdgeMatching_pair
-- name    : MurtySimon.isEdgeMatching_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:02:00.89147+00:00
-- url     : https://prove2.me/theorems/122a3e5e-d5dc-42ba-8abf-f32ff0775fb0
-- title:
--   Murty Simon: is Edge Matching pair
-- statement:
--   The Murty Simon construction uses the is Edge Matching pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Equality.lean#L54-L71
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Equality.lean#L54-L71

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

theorem MurtySimon.isEdgeMatching_pair {a b c d : V} (hab : G.Adj a b) (hcd : G.Adj c d) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) : IsEdgeMatching G {s(a, b), s(c, d)} := by sorry
