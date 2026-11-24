-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TwContraction_step
-- name    : GlobalTheory.CompanionTheory.TwContraction.step
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:18:31.309299+00:00
-- url     : https://prove2.me/theorems/03bcc50c-1459-43c1-a6d0-05bfaff3d1f0
-- title:
--   Tw Contraction: step
-- statement:
--   The Tw Contraction construction uses the step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TwistedIwahoriContractionHolds.lean#L139-L346
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TwistedIwahoriContractionHolds.lean#L139-L346

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedExtensionIntegralBasis
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriFactorization
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TwistedIwahoriContractionHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.Tf.Loc Matrix ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TwContraction
variable {F : Type*} [Field F] [ValuativeRel F] {n : ℕ}

theorem GlobalTheory.CompanionTheory.TwContraction.step (U : Subgroup (GL (Fin n) F)) (hU : (U : Set (GL (Fin n) F)) = iwahori (m := n) F)
    (τ : F ≃+* F) (hτ : ∀ a, valuation F (τ a) = valuation F a)
    (hτU : ∀ g ∈ U, Matrix.GeneralLinearGroup.map (τ : F →+* F) g ∈ U)
    (ρ : ValueGroupWithZero F) (hρ1 : ρ < 1)
    (hunif : ∀ a : F, valuation F a < 1 → valuation F a ≤ ρ)
    (e : Fin n → F) (he : ∀ i, e i ≠ 0)
    (hc : ∀ i l, i < l → valuation F (e i) ≤ ρ * valuation F (e l))
    (x : GL (Fin n) F) (hx : (x : Matrix (Fin n) (Fin n) F) = Matrix.diagonal e)
    (j : ℕ) (c : GL (Fin n) F) (hcU : c ∈ U)
    (hcD : ∀ i l, i ≠ l → valuation F ((c : Matrix (Fin n) (Fin n) F) i l) ≤ ρ ^ j) :
    ∃ p ∈ U, x⁻¹ * p⁻¹ * x * c * Matrix.GeneralLinearGroup.map (τ : F →+* F) p ∈ U ∧
      ∀ i l, i ≠ l → valuation F (((x⁻¹ * p⁻¹ * x * c * Matrix.GeneralLinearGroup.map (τ : F →+* F) p :
        GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i l) ≤ ρ ^ (j + 1) := by sorry
