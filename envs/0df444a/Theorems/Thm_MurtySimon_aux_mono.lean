-- Prove2me | Theorems.Thm_MurtySimon_aux_mono
-- name    : MurtySimon.aux_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:51:25.083109+00:00
-- url     : https://prove2.me/theorems/8d7833ec-be6d-5f51-83bc-b99249496fe2
-- title:
--   Murty Simon: aux mono
-- statement:
--   The Murty Simon construction uses the aux mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Basic.lean#L114-L119
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Basic.lean#L114-L119

module
public import Definitions.Def_MurtySimon_Defs
public import Definitions.Def_MurtySimon_Basic
set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
variable {G}

theorem MurtySimon.aux_mono {M N : Finset (Sym2 V)} (h : N ⊆ M) : aux G M ≤ aux G N := by sorry
