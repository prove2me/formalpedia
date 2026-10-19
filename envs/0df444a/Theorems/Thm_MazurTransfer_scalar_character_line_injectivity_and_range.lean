-- Prove2me | Theorems.Thm_MazurTransfer_scalar_character_line_injectivity_and_range
-- name    : MazurTransfer.scalar_character_line_injectivity_and_range
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T23:49:09.760722+00:00
-- url     : https://prove2.me/theorems/91a04e5b-7058-446c-a27e-bc850274abf7
-- statement:
--   A nonzero character eigenvector defines an injective intertwining map from its one-dimensional scalar representation, with range exactly the line it spans. Both original propositions and all three original universe levels are retained.

import Mathlib
import Definitions.Def_MazurTransfer_ScalarCharacterLineOriginalRepresentationsAndIntertwiningData20261018
noncomputable section
universe u v w
open MazurTransfer.ScalarCharacterLine

theorem MazurTransfer.scalar_character_line_injectivity_and_range :
    (∀ {k : Type u} [Field k] {G : Type v} [Group G] {V : Type w} [AddCommGroup V] [Module k V] (χ : G →* kˣ) (ρ : Representation k G V) (v : V)
    (hv : ∀ g : G, ρ g v = (χ g : k) • v) (hv0 : v ≠ 0) ,
    Function.Injective (vectorIntertwining χ ρ v hv)) ∧
    (∀ {k : Type u} [Field k] {G : Type v} [Group G] {V : Type w} [AddCommGroup V] [Module k V] (χ : G →* kˣ) (ρ : Representation k G V) (v : V)
    (hv : ∀ g : G, ρ g v = (χ g : k) • v) ,
    LinearMap.range (vectorIntertwining χ ρ v hv).toLinearMap = Submodule.span k {v}) := by sorry
