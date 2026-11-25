-- Prove2me | Theorems.Thm_GlobalTheory_ThetaDivisionPoints_exists_ne_zero_of_principal
-- name    : GlobalTheory.ThetaDivisionPoints.exists_ne_zero_of_principal
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T17:36:25.430518+00:00
-- url     : https://prove2.me/theorems/fa996eb3-bac9-448c-8b3f-963e0c4e0741
-- title:
--   Theta Division Points: exists ne zero of principal
-- statement:
--   The Theta Division Points construction uses the exists ne zero of principal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ThetaFunctionNeZeroAtDivisionPointSelfDual.lean#L29-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ThetaFunctionNeZeroAtDivisionPointSelfDual.lean#L29-L88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsThetaDivisionPointNeZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ThetaFunctionNeZeroAtDivisionPointSelfDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open GlobalTheory GlobalTheory.ThetaDivisionPoints

theorem GlobalTheory.ThetaDivisionPoints.exists_ne_zero_of_principal {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (hd : DiscreteTopology Λ) (hs : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (Ef : LinearMap.BilinForm ℤ Λ)
    (hH : Hm.IsHermitian) (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re)
    (hχ : ∀ l, ‖χ l‖ = 1)
    (hE : ∀ l m : Λ, (Ef l m : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im)
    (hbij : Function.Bijective Ef) (n : ℕ) (hn : 2 ≤ n) (f : (Fin g → ℂ) → ℂ)
    (hdf : Differentiable ℂ f) (h0 : f ≠ 0)
    (hf : ∀ (l : Λ) z, f (z + l) = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
      Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) ^ n * f z) :
    ∃ l ∈ Λ, f ((n : ℂ)⁻¹ • l) ≠ 0 := by sorry
