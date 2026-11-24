-- Prove2me | Theorems.Thm_GlobalTheory_evCot_of_univDer
-- name    : GlobalTheory.evCot_of_univDer
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:19:37.577196+00:00
-- url     : https://prove2.me/theorems/b48a0fb4-09c3-4809-8176-9a7ab739ed69
-- title:
--   Global Theory: ev Cot of univ Der
-- statement:
--   The Global Theory construction uses the ev Cot of univ Der property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EvCotOfUnivDer.lean#L33-L350
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EvCotOfUnivDer.lean#L33-L350

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_EvCotStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EvCotOfUnivDer
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
open GlobalTheory
open TensorProduct IsLocalRing Matrix

theorem GlobalTheory.evCot_of_univDer :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : _root_.ReciprocityTheory.PGsh.BX R₀} {Tw : _root_.ReciprocityTheory.PGsh.ATowerL R₀ p} {Dt : _root_.ReciprocityTheory.PGsh.DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : _root_.ReciprocityTheory.PGsh.Be2.Dat p g B Tw Dt Oe σ cp), ∃ δ : ((D.fin.AAx (D.ptIdx 0)) : Type) →+ _root_.ReciprocityTheory.PGsh.Up.LieDualModP p (Tw.O : Type) g,
    (∀ o f, δ ((D.fin.sO (D.ptIdx 0)).1 o * f) = o • δ f) ∧ (∀ f f', δ (f * f') = (D.ptMap 0).1 f • δ f' + (D.ptMap 0).1 f' • δ f) ∧
    (∀ (M : Type) [AddCommGroup M] [Module (Tw.O : Type) M] (d : ((D.fin.AAx (D.ptIdx 0)) : Type) →+ M),
      (∀ o f, d ((D.fin.sO (D.ptIdx 0)).1 o * f) = o • d f) → (∀ f f', d (f * f') = (D.ptMap 0).1 f • d f' + (D.ptMap 0).1 f' • d f) →
      ∃! u : _root_.ReciprocityTheory.PGsh.Up.LieDualModP p (Tw.O : Type) g →ₗ[(Tw.O : Type)] M, ∀ f, d f = u (δ f)) ∧
    ∀ (a : Oe) (α : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx (D.ptIdx 0)) (D.fin.AAx (D.ptIdx 0))), α.comp (D.fin.sO (D.ptIdx 0)) = (D.fin.sO (D.ptIdx 0)) →
      B.map α (D.fin.y (D.ptIdx 0)) = (D.A.act a (D.fin.AAx (D.ptIdx 0)) (D.fin.sO (D.ptIdx 0)) ⟨(D.fin.y (D.ptIdx 0)), (_root_.ReciprocityTheory.PGsh.Be2.mem_torP B p _).2 (D.fin.y_p _)⟩ : B.G (D.fin.AAx (D.ptIdx 0))) →
      ∀ f (l : Fin g → (Tw.O : Type)), δ f = Submodule.Quotient.mk l → δ (α.1 f) = Submodule.Quotient.mk ((D.H.ρL a)ᵀ *ᵥ l)) →
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : _root_.ReciprocityTheory.PGsh.BX R₀} {Tw : _root_.ReciprocityTheory.PGsh.ATowerL R₀ p} {Dt : _root_.ReciprocityTheory.PGsh.DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : _root_.ReciprocityTheory.PGsh.Be2.Dat p g B Tw Dt Oe σ cp), _root_.ReciprocityTheory.PGsh.Be2.EvCotStatement D) := by sorry
