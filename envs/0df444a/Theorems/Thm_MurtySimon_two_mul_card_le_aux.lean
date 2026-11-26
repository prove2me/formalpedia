-- Prove2me | Theorems.Thm_MurtySimon_two_mul_card_le_aux
-- name    : MurtySimon.two_mul_card_le_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:20:34.831985+00:00
-- url     : https://prove2.me/theorems/12757993-9313-418a-a1f9-1b4215daab7f
-- title:
--   Murty Simon: two mul card le aux
-- statement:
--   The Murty Simon construction uses the two mul card le aux property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Main.lean#L143-L151
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Main.lean#L143-L151

module
public import Definitions.Def_MurtySimon_Equality
public import Definitions.Def_MurtySimon_Main
set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj]

theorem MurtySimon.two_mul_card_le_aux (hG : IsDiameterTwoCritical G) {M : Finset (Sym2 V)}
    (hM : IsMaximalEdgeMatching G M) :
    2 * #G.edgeFinset ≤ (Fintype.card V).choose 2 + #M := by sorry
