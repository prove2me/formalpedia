-- Prove2me | Theorems.Thm_MurtySimon_card_Lt_le
-- name    : MurtySimon.card_Lt_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:03:42.599806+00:00
-- url     : https://prove2.me/theorems/501c3eb0-d957-42d2-afe5-2da283079813
-- title:
--   Murty Simon: card Lt le
-- statement:
--   **Lemma 1.2** (internal form): `|E(G) \ M| ≤ |F_c| + |F_nc|`.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Bound.lean#L495-L503
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Bound.lean#L495-L503

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

theorem MurtySimon.card_Lt_le (hmax : IsMaximalEdgeMatching G M) (hG : IsCritical G) :
    #(Lt G M) ≤ #(Rt G) + #(Nc G) := by sorry
