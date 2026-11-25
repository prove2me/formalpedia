-- Prove2me | Theorems.Thm_GlobalTheory_EvHopf_val_add_smul
-- name    : GlobalTheory.EvHopf.val_add_smul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:05:13.347406+00:00
-- url     : https://prove2.me/theorems/549be2db-4e14-5894-a836-8ddfe2573984
-- title:
--   Ev Hopf: val add smul
-- statement:
--   The Ev Hopf construction uses the val add smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EvHopfOfTensorLocal.lean#L34-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EvHopfOfTensorLocal.lean#L34-L38

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_EvHopfStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EvHopfOfTensorLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
set_option linter.style.haveILetI false
open GlobalTheory GlobalTheory.EvHopf
variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp)
variable (C : Type) [Field C] [Algebra (Tw.O : Type) C]

theorem GlobalTheory.EvHopf.val_add_smul {M : Type} [AddCommGroup M] (x : M) (hx : p • x = 0) (a b : ZMod p) :
    (a + b).val • x = a.val • x + b.val • x := by sorry
