-- Prove2me | Theorems.Thm_MurtySimon_lemma_3_3
-- name    : MurtySimon.lemma_3_3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:02:23.03003+00:00
-- url     : https://prove2.me/theorems/0f22f7a9-b9a7-4182-ae0e-c29483b94f0b
-- title:
--   Murty Simon: lemma 3 3
-- statement:
--   **Lemma 3.3.** In an equality case, if a left-lopsided component of `𝓘` has a right vertex,
--   then every edge of `G` contains one fixed vertex (`G` is a star).
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Equality.lean#L189-L344
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Equality.lean#L189-L344

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

theorem MurtySimon.lemma_3_3 (hG : IsCritical G) (heq : EqCase G) (C : (aux G ∅).ConnectedComponent)
    (hC : cA G ∅ C = cB G ∅ C + 1) (hB : 1 ≤ cB G ∅ C) :
    ∃ u, ∀ a b, G.Adj a b → a = u ∨ b = u := by sorry
