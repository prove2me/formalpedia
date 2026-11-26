-- Prove2me | Theorems.Thm_MurtySimon_Recovers_unique
-- name    : MurtySimon.Recovers.unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:59:02.36528+00:00
-- url     : https://prove2.me/theorems/72a5e085-e2af-5b13-bd44-8fd3d225eec4
-- title:
--   Recovers: unique
-- statement:
--   The Recovers construction uses the unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Bound.lean#L210-L221
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Bound.lean#L210-L221

module
public import Definitions.Def_MurtySimon_Components
public import Definitions.Def_MurtySimon_Bound
public import Theorems.Thm_MurtySimon_IsMid_unique

set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
noncomputable section
variable {M : Finset (Sym2 V)}

theorem MurtySimon.Recovers.unique {p : V × V} {ℓ₁ ℓ₂ : Sym2 V} (h₁ : Recovers (G := G) (M := M) p ℓ₁)
    (h₂ : Recovers (G := G) (M := M) p ℓ₂) (hℓ₁ : ℓ₁ ∈ G.edgeSet) (hℓ₂ : ℓ₂ ∈ G.edgeSet) :
    ℓ₁ = ℓ₂ := by sorry
