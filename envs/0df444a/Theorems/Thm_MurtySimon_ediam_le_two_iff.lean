-- Prove2me | Theorems.Thm_MurtySimon_ediam_le_two_iff
-- name    : MurtySimon.ediam_le_two_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:48:31.122924+00:00
-- url     : https://prove2.me/theorems/cc36f9f3-debf-4367-8296-68e42b764387
-- title:
--   Murty Simon: ediam le two iff
-- statement:
--   The Murty Simon construction uses the ediam le two iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Defs.lean#L70-L71
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Defs.lean#L70-L71

module
public import Mathlib
public import Definitions.Def_MurtySimon_Defs
set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open SimpleGraph
variable {V : Type*}

theorem MurtySimon.ediam_le_two_iff (G : SimpleGraph V) : G.ediam ≤ 2 ↔ DiamLeTwo G := by sorry
