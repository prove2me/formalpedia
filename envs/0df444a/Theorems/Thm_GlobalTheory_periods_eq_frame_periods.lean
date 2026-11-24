-- Prove2me | Theorems.Thm_GlobalTheory_periods_eq_frame_periods
-- name    : GlobalTheory.periods_eq_frame_periods
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:14:58.422564+00:00
-- url     : https://prove2.me/theorems/fcb5d5a6-1995-492b-8966-daa682641a76
-- title:
--   Global Theory: periods eq frame periods
-- statement:
--   The Global Theory construction uses the periods eq frame periods property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/PeriodsEqFramePeriods.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/PeriodsEqFramePeriods.lean#L12-L20

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermFormConjDiag
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsFrameOfIsPeriod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PeriodsEqFramePeriods
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory

theorem GlobalTheory.periods_eq_frame_periods : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : (U.Di i).La →ₗ[𝓞 E] (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (idx : Fin g ≃ Ψ × Fin r) (Pf : FD.Frame Ψ r → ((U.Di i).La →+ (Fin g → ℂ))), (∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) → (∀ k, ty k = if ((idx k).2 : ℕ) < (U.Di i).q then ComplexEmbedding.conjugate (idx k).1.1 else (idx k).1.1) → FD.cc ξ = -ξ → (∀ τ ∈ Ψ, 0 < (τ ξ).im) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, (((U.Di i).EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y))) → r = (U.Di i).p + (U.Di i).q → (∀ x v k, Pf x v k = if ((idx k).2 : ℕ) < (U.Di i).q then FD.hermC (idx k).1.1 Gm (FD.col (FD.mat x (idx k).1) (idx k).2) (FD.Data.emb (idx k).1.1 (φ v)) else ((FD.mat x (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 (φ v)) (idx k).2) → (∀ x ∈ FD.GG Ψ Gm (U.Di i).q, IsPeriod (U.Di i) ty (Pf x) ∧ U.u i (Pf x) ≫ Xo.s = spMap σ) ∧ ∀ P, IsPeriod (U.Di i) ty P → ∃ x ∈ FD.GG Ψ Gm (U.Di i).q, Pf x = P := by sorry
