-- Prove2me | Theorems.Thm_HajnalSzemeredi_mem_palette_of_reach
-- name    : HajnalSzemeredi.mem_palette_of_reach
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:45:51.804907+00:00
-- url     : https://prove2.me/theorems/7ad53603-5af7-4f31-8bb2-195691ac3ad9
-- title:
--   Hajnal Szemeredi: mem palette of reach
-- statement:
--   Si `j ≠ lo` alcanza a `lo`, la clase `j` es no vacía y por tanto está en la paleta.
--
--   Source: https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Shift.lean#L33-L40
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Shift.lean#L33-L40

module
public import Definitions.Def_HajnalSzemeredi_Defs
public import Definitions.Def_HajnalSzemeredi_Reach
public import Definitions.Def_HajnalSzemeredi_Shift
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Classical Finset Relation
open HajnalSzemeredi
variable {V : Type*} {G : SimpleGraph V}

theorem HajnalSzemeredi.mem_palette_of_reach {S : Finset V} {P : Finset ℕ} {c : V → ℕ} (hc : Into S c P)
    {R : ℕ → ℕ → Prop} (hR : ∀ a b, R a b → Mov G S c a b) {j lo : ℕ}
    (h : ReflTransGen R j lo) (hj : j ≠ lo) : j ∈ P := by sorry
