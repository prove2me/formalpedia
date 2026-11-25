-- Prove2me | Theorems.Thm_GlobalTheory_OfPeriod_exists_arc
-- name    : GlobalTheory.OfPeriod.exists_arc
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:16:30.76259+00:00
-- url     : https://prove2.me/theorems/c1120aec-a797-49aa-9c4e-4f3f9c0ca2b6
-- title:
--   Of Period: exists arc
-- statement:
--   The Of Period construction uses the exists arc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExpPiIInt.lean#L19-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExpPiIInt.lean#L19-L259

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FinrankHomComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpPiIInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.OfPeriod
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open Complex
variable {W : Type} [AddCommGroup W] [Module ℂ W] [Module ℝ W] [IsScalarTower ℝ ℂ W] [FiniteDimensional ℂ W]
  {S : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ} {O : Type} [CommRing O] [StarRing O]
  {Y M : Type} [AddCommGroup Y] [Module O Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
  [AddCommGroup M] [Module O M] [Module.Free ℤ M] [Module.Finite ℤ M]

theorem GlobalTheory.OfPeriod.exists_arc {w : O} (hw : w + star w = 1) (EM : LinearMap.BilinForm ℤ M) (hEM : Function.Bijective EM)
    (P : Y × (Y →+ ℤ) × M →+ W) (hspan : Submodule.span ℝ (Set.range P) = ⊤)
    (hrk : 2 * Module.finrank ℤ Y + Module.finrank ℤ M = 2 * Module.finrank ℂ W)
    (hconj : ∀ z w, starRingEnd ℂ (S z w) = S w z) (hpos : ∀ z, z ≠ 0 → 0 < (S z z).re)
    (hS : ∀ v v', (S (P v) (P v')).im = (v'.2.1 v.1 - v.2.1 v'.1 + EM v.2.2 v'.2.2 : ℤ))
    (ρ : O →+* Module.End ℂ W) (hρ : ∀ a z w, S (ρ a z) w = S z (ρ (star a) w))
    (hP : ∀ (a : O) v, P (a • v.1, v.2.1.comp (DistribSMul.toAddMonoidHom Y (star a)), a • v.2.2) = ρ a (P v))
    (be : LinearMap.BilinForm ℤ Y) (be_symm : ∀ x y, be x y = be y x) (be_pos : ∀ x, x ≠ 0 → 0 < be x x)
    (be_adj : ∀ (a : O) y x, be (a • y) x = be y (star a • x)) (be_even : ∀ x, (2 : ℤ) ∣ be x x)
    (Q : ∀ n : ℕ, (O →+* Module.End ℂ (Fin n → ℂ)) → Prop)
    (hQ : ∀ (U : Type) [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U] (σ : O →+* Module.End ℂ U),
      ∃ (n : ℕ) (k : U ≃ₗ[ℂ] (Fin n → ℂ)) (F : O →+* Module.End ℂ (Fin n → ℂ)), Q n F ∧ ∀ a u, k (σ a u) = F a (k u)) :
    ∃ (A : AnArc O) (e : A.X ≃ₗ[O] Y) (f : M ≃+ A.abelian₂) (h : W ≃ₗ[ℂ] A.V),
      (∀ x y, A.be x y = be (e x) (e y)) ∧ (∀ l, A.chi l = (-1) ^ A.Ef (A.FLam w l) l) ∧
      (∀ x, (A.psi x : ℂ) = eTwoPi (A.T x (w • x))) ∧ Q A.gB A.F ∧ (∀ (a : O) m, f (a • m) = A.FLam a (f m)) ∧
      (∀ m m', A.Ef (f m) (f m') = EM m m') ∧ (∀ a z, h (ρ a z) = A.actV a (h z)) ∧
      (∀ v, h (P v) = A.P0 (AnArc.La.mk (e.symm v.1) (v.2.1.comp e.toAddEquiv.toAddMonoidHom) (f v.2.2))) ∧
      (A.BwMat 0).PosDef := by sorry
