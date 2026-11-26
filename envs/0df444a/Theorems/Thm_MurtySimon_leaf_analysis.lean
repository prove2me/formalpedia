-- Prove2me | Theorems.Thm_MurtySimon_leaf_analysis
-- name    : MurtySimon.leaf_analysis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:59:50.752987+00:00
-- url     : https://prove2.me/theorems/1fe39381-0724-4207-a8d5-1e7b58ebae6e
-- title:
--   Murty Simon: leaf analysis
-- statement:
--   The analysis of one leaf in the proof of **Lemma 2.11**: either the component has weight at
--   least two, or the leaf produces a switch exit from which the leaf can be recovered.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Bound.lean#L315-L437
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Bound.lean#L315-L437

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
variable (hM : IsEdgeMatching G M) {C : (aux G M).ConnectedComponent}
  (hC : cA G M C = cB G M C + 1)
include hM hC

theorem MurtySimon.leaf_analysis (hmax : IsMaximalEdgeMatching G M) {ℓ : Sym2 V} (hℓL : ℓ ∈ Lt G M)
    (hℓC : (aux G M).connectedComponentMk ℓ = C) (hℓd : #((aux G M).neighborFinset ℓ) = 1) :
    2 ≤ compWt C ∨ ∃ p ∈ exits G M, compOf G M p = C ∧ Recovers (G := G) (M := M) p ℓ := by sorry
