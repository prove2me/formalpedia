-- Prove2me | Theorems.Thm_MurtySimon_main_chain
-- name    : MurtySimon.main_chain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:58:25.452497+00:00
-- url     : https://prove2.me/theorems/824454b7-9fba-5f54-837e-f690c244ef12
-- title:
--   Murty Simon: main chain
-- statement:
--   The chain of inequalities of Section 2, with the quantities needed for the equality case:
--   `|E'| − |F_c| ≤ |C_ℓ| ≤ |F_nc|`, where `C_ℓ` is the set of left-lopsided components.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Bound.lean#L469-L492
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Bound.lean#L469-L492

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

theorem MurtySimon.main_chain (hmax : IsMaximalEdgeMatching G M) (hG : IsCritical G) :
    (#(Lt G M) : ℤ) - #(Rt G) =
      ∑ C, ((cA G M C : ℤ) - cB G M C) ∧
    (∀ C, ((cA G M C : ℤ) - cB G M C) ≤ if cA G M C = cB G M C + 1 then 1 else 0) ∧
    2 * #((univ : Finset (aux G M).ConnectedComponent).filter fun C => cA G M C = cB G M C + 1)
      + ∑ C ∈ (univ : Finset (aux G M).ConnectedComponent).filter
          (fun C => ¬ cA G M C = cB G M C + 1), compWt (G := G) (M := M) C
      ≤ 2 * #(Nc G) := by sorry
