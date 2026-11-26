-- Prove2me | Theorems.Thm_MurtySimon_eq_case_conditions
-- name    : MurtySimon.eq_case_conditions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:59:41.576963+00:00
-- url     : https://prove2.me/theorems/d641fcd3-ae9c-463f-abe4-e4b1d7c2e656
-- title:
--   Murty Simon: eq case conditions
-- statement:
--   **Corollary 2.14.** In the equality case no component is right-lopsided and no balanced
--   component has a switch exit.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Bound.lean#L507-L538
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Bound.lean#L507-L538

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

theorem MurtySimon.eq_case_conditions (hmax : IsMaximalEdgeMatching G M) (hG : IsCritical G)
    (heq : #(Lt G M) = #(Rt G) + #(Nc G)) :
    (∀ C, cB G M C ≤ cA G M C) ∧
    (∀ C, cA G M C = cB G M C → ∀ p ∈ exits G M, compOf G M p ≠ C) := by sorry
