-- Prove2me | Theorems.Thm_GlobalTheory_chowla_selberg
-- name    : GlobalTheory.chowla_selberg
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:44:15.261656+00:00
-- url     : https://prove2.me/theorems/bf6ead34-8081-46ff-9f60-be0bd3d41858
-- title:
--   Global Theory: chowla selberg
-- statement:
--   The Global Theory construction uses the chowla selberg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/DedekindZetaEqSumRealEisenstein.lean#L325-L346
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/DedekindZetaEqSumRealEisenstein.lean#L325-L346

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoRealEisensteinSubPole
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DedekindZetaEqSumRealEisenstein
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module FractionalIdeal Filter Topology
open scoped nonZeroDivisors UpperHalfPlane Real
open GlobalTheory
open QuadraticZeta
variable {K : Type*} [Field K] [NumberField K] {d : ℕ}

theorem GlobalTheory.chowla_selberg [NeZero d] (h2 : finrank ℚ K = 2) (hD : discr K = -d) (hd : 4 < d)
    {χ : DirichletCharacter ℂ d} (hχ : IsKroneckerChar χ) (σ : K →+* ℂ) :
    (∀ s : ℂ, 1 < s.re → dedekindZeta K s = riemannZeta s * χ.LFunction s) ∧
    χ.LFunction 1 = (π * classNumber K / √d : ℝ) ∧
    (∀ τ : ClassGroup (𝓞 K) → ℍ, (∀ c, IsIdealClassPoint σ c (τ c)) →
      (((∑ c, Real.log (4 * π * (τ c).im * ‖ModularForm.eta (τ c)‖ ^ 4)) / classNumber K : ℝ) : ℂ)
        = (Real.eulerMascheroniConstant + Real.log (2 * π / √d) : ℝ)
          - deriv χ.LFunction 1 / χ.LFunction 1) ∧
    ∀ (𝔞 : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (L : ClassGroup (𝓞 K) → PeriodPair),
      (∀ c, ClassGroup.mk K (𝔞 c) = c) → (∀ c, ((L c).lattice : Set ℂ) = σ '' (𝔞 c).1) →
      (((∑ c, latticeLogPeriod (L c)) / classNumber K : ℝ) : ℂ)
        = (Real.eulerMascheroniConstant + Real.log (2 * π / √d) : ℝ)
          - deriv χ.LFunction 1 / χ.LFunction 1 ∧
      (((∑ c, Real.log ((absNorm (𝔞 c).1 : ℝ) ^ 6 * ‖(L c).g₂ ^ 3 - 27 * (L c).g₃ ^ 2‖))
          / classNumber K : ℝ) : ℂ)
        = (12 * Real.log (2 * π) - 6 * Real.log d + 6 * Real.eulerMascheroniConstant : ℝ)
          - 6 * (deriv χ.LFunction 1 / χ.LFunction 1) := by sorry
