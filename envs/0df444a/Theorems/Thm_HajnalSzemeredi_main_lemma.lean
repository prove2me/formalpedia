-- Prove2me | Theorems.Thm_HajnalSzemeredi_main_lemma
-- name    : HajnalSzemeredi.main_lemma
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:47:45.312918+00:00
-- url     : https://prove2.me/theorems/22644176-9add-4521-9239-4a3911c49c26
-- title:
--   Hajnal Szemeredi: main lemma
-- statement:
--   Lema principal (inducción secundaria en el número de clases inaccesibles).
--
--   Source: https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Main.lean#L76-L109
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Main.lean#L76-L109

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

theorem HajnalSzemeredi.main_lemma {S : Finset V} {P : Finset ℕ} {r s lo : ℕ}
    (IH : ∀ S' ⊆ S, edgeCount G S' < edgeCount G S → ∀ (P' : Finset ℕ) (r' : ℕ),
      P'.card = r' + 1 → S'.card = s * (r' + 1) → DegLe G S' r' → ∃ c, IsEq G S' P' c s)
    (hdeg : DegLe G S r) (hP : P.card = r + 1) :
    ∀ (c : V → ℕ) (hi : ℕ), IsNear G S P c s lo hi → ∃ c', IsEq G S P c' s := by sorry
