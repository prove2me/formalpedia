-- Prove2me | Theorems.Thm_MurtySimon_diamLeTwo_iff_edist
-- name    : MurtySimon.diamLeTwo_iff_edist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:48:23.85359+00:00
-- url     : https://prove2.me/theorems/fb8224a3-8cd7-5768-b79e-b6b645a23c45
-- title:
--   Murty Simon: diam Le Two iff edist
-- statement:
--   The Murty Simon construction uses the diam Le Two iff edist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Defs.lean#L47-L68
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Defs.lean#L47-L68

module
public import Mathlib
public import Definitions.Def_MurtySimon_Defs
set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open SimpleGraph
variable {V : Type*}

theorem MurtySimon.diamLeTwo_iff_edist (G : SimpleGraph V) : DiamLeTwo G ↔ ∀ u v, G.edist u v ≤ 2 := by sorry
