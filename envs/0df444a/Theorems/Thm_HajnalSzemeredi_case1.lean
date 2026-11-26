-- Prove2me | Theorems.Thm_HajnalSzemeredi_case1
-- name    : HajnalSzemeredi.case1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:47:35.863541+00:00
-- url     : https://prove2.me/theorems/e8856fd1-762b-45c6-a8cd-b08f97131e49
-- title:
--   Hajnal Szemeredi: case1
-- statement:
--   The Hajnal Szemeredi construction uses the case1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Cases.lean#L181-L306
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Cases.lean#L181-L306

module
public import Definitions.Def_HajnalSzemeredi_Shift
public import Definitions.Def_HajnalSzemeredi_Structure
public import Definitions.Def_HajnalSzemeredi_Cases
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Classical Finset Relation
open HajnalSzemeredi
variable {V : Type*} {G : SimpleGraph V}

theorem HajnalSzemeredi.case1 {S : Finset V} {P : Finset ℕ} {c g : V → ℕ} {r s lo hi U : ℕ} {z y₁ : V}
    (h : Ctx G S P c r s lo hi)
    (hterm : ∀ W ∈ T G S P c lo U, ∀ X ∈ (acc G S P c lo).erase W,
      ReflTransGen (avoid G S c W) X lo)
    (hzS : z ∈ S) (hzT : c z ∈ T G S P c lo U)
    (hy₁ : y₁ ∈ Sz G S c (T G S P c lo U) (part S c (P \ acc G S P c lo)) z)
    (hX : ∃ X ∈ acc G S P c lo, X ≠ c z ∧ Movable G S c z X)
    (hg : IsEq G ((part S c (P \ acc G S P c lo)).erase y₁) (P \ acc G S P c lo) g s) :
    ∃ c', IsEq G S P c' s := by sorry
