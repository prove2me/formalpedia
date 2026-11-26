-- Prove2me | Theorems.Thm_HajnalSzemeredi_bminus
-- name    : HajnalSzemeredi.bminus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:47:39.489689+00:00
-- url     : https://prove2.me/theorems/3976cacc-34e9-4d80-a787-4ef196ba54d9
-- title:
--   Hajnal Szemeredi: bminus
-- statement:
--   Hechos sobre `B⁻ = B \ {y₁}` necesarios para aplicar la hipótesis de inducción primaria.
--
--   Source: https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Main.lean#L31-L73
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Main.lean#L31-L73

module
public import Definitions.Def_HajnalSzemeredi_Cases
public import Definitions.Def_HajnalSzemeredi_Main
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Classical Finset Relation
open HajnalSzemeredi
variable {V : Type*} {G : SimpleGraph V}

theorem HajnalSzemeredi.bminus {S : Finset V} {P : Finset ℕ} {c : V → ℕ} {r s lo hi : ℕ} {TU : Finset ℕ}
    (h : Ctx G S P c r s lo hi)
    (hch : CountHyp G S c (acc G S P c lo) (P \ acc G S P c lo) TU r s) {y₁ : V}
    (hy₁ : y₁ ∈ part S c (P \ acc G S P c lo)) :
    (part S c (P \ acc G S P c lo)).erase y₁ ⊆ S ∧
    edgeCount G ((part S c (P \ acc G S P c lo)).erase y₁) < edgeCount G S ∧
    ((part S c (P \ acc G S P c lo)).erase y₁).card =
      s * ((P \ acc G S P c lo).card - 1 + 1) ∧
    DegLe G ((part S c (P \ acc G S P c lo)).erase y₁) ((P \ acc G S P c lo).card - 1) := by sorry
