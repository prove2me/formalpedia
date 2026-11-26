-- Prove2me | Theorems.Thm_HajnalSzemeredi_case2
-- name    : HajnalSzemeredi.case2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:47:35.966411+00:00
-- url     : https://prove2.me/theorems/28c924e9-7739-43d9-bd59-4bb341ba6739
-- title:
--   Hajnal Szemeredi: case2
-- statement:
--   The Hajnal Szemeredi construction uses the case2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Cases.lean#L308-L541
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Cases.lean#L308-L541

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

theorem HajnalSzemeredi.case2 {S : Finset V} {P : Finset ℕ} {c g : V → ℕ} {r s lo hi U : ℕ} {z y₁ y₂ : V}
    (h : Ctx G S P c r s lo hi)
    (hterm : ∀ W ∈ T G S P c lo U, ∀ X ∈ (acc G S P c lo).erase W,
      ReflTransGen (avoid G S c W) X lo)
    (hzS : z ∈ S) (hzT : c z ∈ T G S P c lo U)
    (hnot : ∀ X ∈ acc G S P c lo, X ≠ c z → ¬ Movable G S c z X)
    (hy₁ : y₁ ∈ Sz G S c (T G S P c lo U) (part S c (P \ acc G S P c lo)) z)
    (hy₂ : y₂ ∈ Sz G S c (T G S P c lo U) (part S c (P \ acc G S P c lo)) z)
    (hne : y₁ ≠ y₂) (hnadj : ¬ G.Adj y₁ y₂)
    (hg : IsEq G ((part S c (P \ acc G S P c lo)).erase y₁) (P \ acc G S P c lo) g s) :
    ∃ c' hi', IsNear G S P c' s lo hi' ∧
      (acc G S P c lo).card < (acc G S P c' lo).card := by sorry
