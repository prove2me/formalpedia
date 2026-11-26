-- Prove2me | Theorems.Thm_MurtySimon_IsDiameterTwoCritical_isCritical
-- name    : MurtySimon.IsDiameterTwoCritical.isCritical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:48:30.295339+00:00
-- url     : https://prove2.me/theorems/ced0a528-4c7e-4599-ae2f-32319a32a2a2
-- title:
--   Is Diameter Two Critical: is Critical
-- statement:
--   The Is Diameter Two Critical construction uses the is Critical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Defs.lean#L77-L81
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Defs.lean#L77-L81

module
public import Mathlib
public import Definitions.Def_MurtySimon_Defs
set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open SimpleGraph
variable {V : Type*}

theorem MurtySimon.IsDiameterTwoCritical.isCritical {G : SimpleGraph V} (h : IsDiameterTwoCritical G) :
    IsCritical G := by sorry
