-- Prove2me | Theorems.Thm_GlobalTheory_localFactor_mod_p_nilOver
-- name    : GlobalTheory.localFactor_mod_p_nilOver
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:11:26.451529+00:00
-- url     : https://prove2.me/theorems/6fbe37ad-c2b0-46fb-bd5e-813bfd9b490d
-- title:
--   Global Theory: local Factor mod p nil Over
-- statement:
--   The Global Theory construction uses the local Factor mod p nil Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LocalFactorModPNilOver.lean#L175-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LocalFactorModPNilOver.lean#L175-L222

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_ATowerInh
import Definitions.Def_ReciprocityTheory_DualLattices_AinfFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LocalFactorModPNilOver
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
open GlobalTheory
open TensorProduct IsLocalRing Matrix

theorem GlobalTheory.localFactor_mod_p_nilOver :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : _root_.ReciprocityTheory.PGsh.BX R₀} {Tw : _root_.ReciprocityTheory.PGsh.ATowerL R₀ p} {Dt : _root_.ReciprocityTheory.PGsh.DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : _root_.ReciprocityTheory.PGsh.Be2.Dat p g B Tw Dt Oe σ cp), 0 < g → maximalIdeal (D.K : Type) = ⊥ ∧ _root_.ReciprocityTheory.PGsh.Be2.IsNilOver D.wd.ρ1 ∧ ∀ i : D.fin.ι,
    ∃ (Λ : _root_.ReciprocityTheory.PGsh.LAlg R₀) (μ : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx i) Λ) (j : _root_.ReciprocityTheory.PGsh.LHom (Tw.R 0) Λ) (ρΛ : _root_.ReciprocityTheory.PGsh.LHom Λ D.K),
      _root_.ReciprocityTheory.PGsh.Be2.IsNilOver ρΛ ∧ Function.Surjective μ.1 ∧ ρΛ.comp j = D.wd.ρ1 ∧ μ.comp (D.fin.sO i) = j.comp (Tw.q 0) ∧
      ∀ φ : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx i) Tw.O, φ.comp (D.fin.sO i) = _root_.ReciprocityTheory.PGsh.LHom.id Tw.O →
        ∃ ψ : _root_.ReciprocityTheory.PGsh.LHom Λ (Tw.R 0), ψ.comp μ = (Tw.q 0).comp φ ∧ ψ.comp j = _root_.ReciprocityTheory.PGsh.LHom.id (Tw.R 0) ∧ D.wd.ρ1.comp ψ = ρΛ) := by sorry
