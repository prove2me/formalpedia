-- Prove2me | Theorems.Thm_GlobalTheory_CotPoints_points_eq_tangent
-- name    : GlobalTheory.CotPoints.points_eq_tangent
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:27:22.151522+00:00
-- url     : https://prove2.me/theorems/5ee3bc7b-2a68-44af-8b0b-ed2257eec04b
-- title:
--   Cot Points: points eq tangent
-- statement:
--   The Cot Points construction uses the points eq tangent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PointsEqTangent.lean#L49-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PointsEqTangent.lean#L49-L88

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_EvCotStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PointsEqTangent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
open GlobalTheory GlobalTheory.CotPoints

theorem GlobalTheory.CotPoints.points_eq_tangent :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp), ∀ (S : LAlg R₀) (s : LHom Tw.O S) (π : LHom S Tw.O) (hπ : π.SqZero), π.comp s = LHom.id Tw.O →
    (∀ m : Fin g → π.ker, (∀ k, p • m k = 0) → ∃! φ : LHom (D.fin.AAx (D.ptIdx 0)) S, φ.comp (D.fin.sO (D.ptIdx 0)) = s ∧ π.comp φ = (D.ptMap 0) ∧
      B.map φ (D.fin.y (D.ptIdx 0)) = B.tg π hπ (∑ k, D.ch.gb k ⊗ₜ[R₀] m k)) ∧
    (∀ φ : LHom (D.fin.AAx (D.ptIdx 0)) S, φ.comp (D.fin.sO (D.ptIdx 0)) = s → π.comp φ = (D.ptMap 0) → ∃! m : Fin g → π.ker, (∀ k, p • m k = 0) ∧
      B.map φ (D.fin.y (D.ptIdx 0)) = B.tg π hπ (∑ k, D.ch.gb k ⊗ₜ[R₀] m k))) := by sorry
