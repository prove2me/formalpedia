-- Prove2me | Theorems.Thm_MurtySimon_comp_count
-- name    : MurtySimon.comp_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:53:23.08419+00:00
-- url     : https://prove2.me/theorems/980d44db-b310-5cf3-9d14-9a3e0d0132ba
-- title:
--   Murty Simon: comp count
-- statement:
--   **Lemma 2.4** of Das–Fox, in counting form.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Components.lean#L92-L261
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Components.lean#L92-L261

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

theorem MurtySimon.comp_count (M : Finset (Sym2 V)) (C : (aux G M).ConnectedComponent) :
    cA G M C ≤ cB G M C + 1 ∧
    (cA G M C = cB G M C + 1 →
      (∀ f ∈ Rt G, (aux G M).connectedComponentMk f = C →
        #((aux G M).neighborFinset f) = 2) ∧
      (2 ≤ cA G M C → ∃ l₁ ∈ Lt G M, ∃ l₂ ∈ Lt G M, l₁ ≠ l₂ ∧
        (aux G M).connectedComponentMk l₁ = C ∧ (aux G M).connectedComponentMk l₂ = C ∧
        #((aux G M).neighborFinset l₁) = 1 ∧ #((aux G M).neighborFinset l₂) = 1)) := by sorry
