-- Prove2me | Theorems.Thm_GlobalTheory_EvHopf_evHopf_of_tensorLocal
-- name    : GlobalTheory.EvHopf.evHopf_of_tensorLocal
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:59:37.329327+00:00
-- url     : https://prove2.me/theorems/cb007906-d6b1-4ebd-9290-369a9b7417b1
-- title:
--   Ev Hopf: ev Hopf of tensor Local
-- statement:
--   The Ev Hopf construction uses the ev Hopf of tensor Local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EvHopfOfTensorLocal.lean#L327-L364
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EvHopfOfTensorLocal.lean#L327-L364

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
open TensorProduct IsLocalRing Matrix
set_option linter.style.haveILetI false
variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : _root_.ReciprocityTheory.PGsh.BX R₀} {Tw : _root_.ReciprocityTheory.PGsh.ATowerL R₀ p} {Dt : _root_.ReciprocityTheory.PGsh.DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)} (D : _root_.ReciprocityTheory.PGsh.Be2.Dat p g B Tw Dt Oe σ cp)
variable (C : Type) [Field C] [Algebra (Tw.O : Type) C]

theorem GlobalTheory.EvHopf.evHopf_of_tensorLocal :
  (∀ (O A A' : Type) [CommRing O] [CommRing A] [CommRing A'] [IsLocalRing O] [IsLocalRing A] [IsLocalRing A'] [Algebra O A] [Algebra O A']
    [Module.Finite O A] [Module.Finite O A'], (A →ₐ[O] O) → (A' →ₐ[O] O) → IsLocalRing (A ⊗[O] A')) →
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : _root_.ReciprocityTheory.PGsh.BX R₀} {Tw : _root_.ReciprocityTheory.PGsh.ATowerL R₀ p} {Dt : _root_.ReciprocityTheory.PGsh.DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : _root_.ReciprocityTheory.PGsh.Be2.Dat p g B Tw Dt Oe σ cp), _root_.ReciprocityTheory.PGsh.Be2.EvHopfStatement D) := by sorry
